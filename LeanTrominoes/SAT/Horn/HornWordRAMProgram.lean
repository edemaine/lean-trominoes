/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Arrays
import LeanTrominoes.SAT.Horn.HornIndexedSolver

/-! # A concrete bounded-word RAM program for Horn satisfiability

The input contains the variable/rule/occurrence counts, rule heads, and the
premise-occurrence stream in two parallel arrays. Atom zero denotes false;
variable i has code i+1. No occurrence index, initial counters, or answer is
precomputed by the encoding. The program constructs the occurrence index,
then propagates ready rule heads using an array stack. Duplicate premises are
retained. Five allocated arrays store seen flags, buckets, counters, links,
and the work stack.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

abbrev Input := Σ n : ℕ, Indexed.Input n

def atomCode {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some i => i.val+1

def words (input : Input) : List ℕ :=
  let rules := input.2.rules
  let edges := Indexed.edges input.2
  [input.1,rules.size,edges.length] ++
    (List.finRange rules.size).map (fun i => atomCode rules[i].conclusion) ++
    edges.map (fun ar => atomCode ar.1) ++ edges.map (fun ar => ar.2.val)

def encode (input : Input) : List ℤ := (words input).map Int.ofNat

def size (input : Input) : ℕ := input.1+input.2.rules.size+(Indexed.edges input.2).length+1

theorem words_length (input : Input) :
    (words input).length=3+input.2.rules.size+2*(Indexed.edges input.2).length := by
  simp [words]
  omega

namespace Reg
abbrev heap : Fin 32 := 0
abbrev request : Fin 32 := 1
abbrev allocated : Fin 32 := 2
abbrev cursor : Fin 32 := 3
abbrev zero : Fin 32 := 4
abbrev one : Fin 32 := 5
abbrev atoms : Fin 32 := 6
abbrev rules : Fin 32 := 7
abbrev occurrences : Fin 32 := 8
abbrev heads : Fin 32 := 9
abbrev edgeAtoms : Fin 32 := 10
abbrev edgeRules : Fin 32 := 11
abbrev seen : Fin 32 := 12
abbrev buckets : Fin 32 := 13
abbrev counters : Fin 32 := 14
abbrev links : Fin 32 := 15
abbrev stack : Fin 32 := 16
abbrev index : Fin 32 := 17
abbrev atom : Fin 32 := 18
abbrev rule : Fin 32 := 19
abbrev value : Fin 32 := 20
abbrev top : Fin 32 := 21
abbrev event : Fin 32 := 22
abbrev scratch : Fin 32 := 23
abbrev headValue : Fin 32 := 24
abbrev output : Fin 32 := 25
end Reg

abbrev Code := Structured.Code 32

def constant (dst : Fin 32) (value : ℕ) : Code := .atom (.constant dst value)
def copy (dst src : Fin 32) : Code := .atom (.copy dst src)
def add (dst a b : Fin 32) : Code := .atom (.arithmetic .add dst a b)
def increment (dst : Fin 32) : Code := add dst dst Reg.one
def decrement (dst : Fin 32) : Code := .atom (.arithmetic .sub dst dst Reg.one)
def read (dst pointer index : Fin 32) : Code := Allocation.readProgram Reg.scratch dst pointer index
def write (src pointer index : Fin 32) : Code := Allocation.writeProgram Reg.scratch src pointer index

def skip : Code := copy Reg.zero Reg.zero

def allocate (dst length : Fin 32) : Code :=
  .seq (copy Reg.request length) <|
  .seq (Allocation.program 26) (copy dst Reg.allocated)

/-- Input pointers are established by reading the three header words. -/
def headerProgram : Code :=
  .seq (Allocation.initializeProgram 26) <|
  .seq (constant Reg.scratch 1) <|
  .seq (.atom (.load Reg.atoms Reg.scratch)) <|
  .seq (increment Reg.atoms) <|
  .seq (constant Reg.scratch 2) <|
  .seq (.atom (.load Reg.rules Reg.scratch)) <|
  .seq (constant Reg.scratch 3) <|
  .seq (.atom (.load Reg.occurrences Reg.scratch)) <|
  .seq (constant Reg.heads 4) <|
  .seq (add Reg.edgeAtoms Reg.heads Reg.rules) (add Reg.edgeRules Reg.edgeAtoms Reg.occurrences)

def prepare : Code := .seq headerProgram <|
  .seq (allocate Reg.seen Reg.atoms) <|
  .seq (allocate Reg.buckets Reg.atoms) <|
  .seq (allocate Reg.counters Reg.rules) <|
  .seq (allocate Reg.links Reg.occurrences) (allocate Reg.stack Reg.rules)

/-- Each occurrence installs a link in its atom's bucket and increments its
rule's counter. Occurrence indices in links are shifted by one; zero ends a list. -/
def indexBody : Code :=
  .seq (read Reg.atom Reg.edgeAtoms Reg.index) <|
  .seq (read Reg.rule Reg.edgeRules Reg.index) <|
  .seq (read Reg.value Reg.buckets Reg.atom) <|
  .seq (write Reg.value Reg.links Reg.index) <|
  .seq (add Reg.value Reg.index Reg.one) <|
  .seq (write Reg.value Reg.buckets Reg.atom) <|
  .seq (read Reg.value Reg.counters Reg.rule) <|
  .seq (increment Reg.value) <|
  .seq (write Reg.value Reg.counters Reg.rule) (increment Reg.index)

def buildIndex : Code := .seq (constant Reg.index 0)
  (.loop (.lt Reg.index Reg.occurrences) indexBody)

def pushHead : Code :=
  .seq (read Reg.headValue Reg.heads Reg.rule) <|
  .seq (write Reg.headValue Reg.stack Reg.top) (increment Reg.top)

def initialStackBody : Code :=
  .seq (read Reg.value Reg.counters Reg.index) <|
  .seq (.branch (.eq Reg.value Reg.zero)
    (.seq (copy Reg.rule Reg.index) pushHead) skip) (increment Reg.index)

def initialStack : Code :=
  .seq (constant Reg.top 0) <|
  .seq (constant Reg.index 0) (.loop (.lt Reg.index Reg.rules) initialStackBody)

/-- Each premise occurrence is processed once, when its atom is first marked.
A rule head is pushed only when its counter changes from one to zero. -/
def eventBody : Code :=
  .seq (decrement Reg.event) <|
  .seq (read Reg.rule Reg.edgeRules Reg.event) <|
  .seq (read Reg.value Reg.counters Reg.rule) <|
  .seq (.branch (.eq Reg.value Reg.zero) skip
    (.seq (decrement Reg.value) <|
      .seq (write Reg.value Reg.counters Reg.rule)
        (.branch (.eq Reg.value Reg.zero) pushHead skip)))
    (read Reg.event Reg.links Reg.event)

def processEvents : Code := .loop (.lt Reg.zero Reg.event) eventBody

def popBody : Code :=
  .seq (decrement Reg.top) <|
  .seq (read Reg.atom Reg.stack Reg.top) <|
  .seq (read Reg.value Reg.seen Reg.atom)
    (.branch (.eq Reg.value Reg.zero)
      (.seq (constant Reg.value 1) <|
        .seq (write Reg.value Reg.seen Reg.atom) <|
        .seq (read Reg.event Reg.buckets Reg.atom) processEvents) skip)

def propagate : Code := .loop (.lt Reg.zero Reg.top) popBody

def answer : Code := .seq (read Reg.value Reg.seen Reg.zero)
  (.branch (.eq Reg.value Reg.zero) (constant Reg.output 1) (constant Reg.output 0))

def program : Code := .seq prepare <| .seq buildIndex <| .seq initialStack <| .seq propagate answer

def bytecode : List (Instruction 32) := program.program Reg.output

end LeanTrominoes.Horn.WordRAM
