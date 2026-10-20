/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalAllocation
import LeanTrominoes.Computation.RAM.Arrays
import LeanTrominoes.Computation.RAM.StructuredCompile
import LeanTrominoes.Graphs.Matching.PeriodicMatchingSolver

/-! # A fixed bounded-word RAM program for dense bipartite matching

The original encoding consists of vertex counts, an edge count, and two
endpoint arrays. Each discovered left vertex stores a complete alternating
prefix in a row of a quadratic table. This uses polynomial time and space;
no graph index, matching, path, or decision answer occurs in the input.
-/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

abbrev Input := Σ n : Nat, Σ m : Nat, List (Fin n × Fin m)

def words (input : Input) : List Nat :=
  [input.1,input.2.1,input.2.2.length]++input.2.2.map (fun e => e.1.val)++input.2.2.map (fun e => e.2.val)
def encode (input : Input) := (words input).map Int.ofNat
def size (input : Input) := input.1+input.2.1+input.2.2.length+1

namespace Reg
abbrev heap : Fin 64 := 0
abbrev request : Fin 64 := 1
abbrev allocated : Fin 64 := 2
abbrev cursor : Fin 64 := 3
abbrev zero : Fin 64 := 4
abbrev one : Fin 64 := 5
abbrev n : Fin 64 := 6
abbrev m : Fin 64 := 7
abbrev edges : Fin 64 := 8
abbrev edgeLeft : Fin 64 := 9
abbrev edgeRight : Fin 64 := 10
abbrev partnerLeft : Fin 64 := 11
abbrev partnerRight : Fin 64 := 12
abbrev lengths : Fin 64 := 13
abbrev rowLeft : Fin 64 := 14
abbrev rowRight : Fin 64 := 15
abbrev cells : Fin 64 := 16
abbrev outer : Fin 64 := 17
abbrev round : Fin 64 := 18
abbrev index : Fin 64 := 19
abbrev left : Fin 64 := 20
abbrev right : Fin 64 := 21
abbrev mate : Fin 64 := 22
abbrev length : Fin 64 := 23
abbrev value : Fin 64 := 24
abbrev source : Fin 64 := 25
abbrev target : Fin 64 := 26
abbrev copyIndex : Fin 64 := 27
abbrev rowIndex : Fin 64 := 28
abbrev foundLeft : Fin 64 := 29
abbrev foundRight : Fin 64 := 30
abbrev output : Fin 64 := 31
abbrev scratch : Fin 64 := 32
end Reg

abbrev Code := Structured.Code 64

def constant (dst : Fin 64) (n : Nat) : Code := .atom (.constant dst n)
def copy (dst src : Fin 64) : Code := .atom (.copy dst src)
def add (dst a b : Fin 64) : Code := .atom (.arithmetic .add dst a b)
def sub (dst a b : Fin 64) : Code := .atom (.arithmetic .sub dst a b)
def mul (dst a b : Fin 64) : Code := .atom (.arithmetic .mul dst a b)
def increment (dst : Fin 64) := add dst dst Reg.one
def decrement (dst : Fin 64) := sub dst dst Reg.one
def read (base index dst : Fin 64) : Code := Allocation.readProgram Reg.scratch dst base index
def write (base index value : Fin 64) : Code := Allocation.writeProgram Reg.scratch value base index
def skip : Code := copy Reg.zero Reg.zero
def allocate (dst length : Fin 64) : Code :=
  .seq (copy Reg.request length) (.seq (Allocation.program 58) (copy dst Reg.allocated))

def header : Code := .seq (Allocation.initializeProgram 58)
  (.seq (constant Reg.cursor 1) (.seq (.atom (.load Reg.n Reg.cursor))
  (.seq (increment Reg.cursor) (.seq (.atom (.load Reg.m Reg.cursor))
  (.seq (increment Reg.cursor) (.seq (.atom (.load Reg.edges Reg.cursor))
  (.seq (constant Reg.edgeLeft 4) (.seq (add Reg.edgeRight Reg.edgeLeft Reg.edges)
    (mul Reg.cells Reg.n Reg.n)))))))))

def prepare : Code := .seq header
  (.seq (allocate Reg.partnerLeft Reg.n) (.seq (allocate Reg.partnerRight Reg.m)
  (.seq (allocate Reg.lengths Reg.n) (.seq (allocate Reg.rowLeft Reg.cells)
    (allocate Reg.rowRight Reg.cells)))))

/-- Source rows contain prefix pairs. A zero row length means unreached;
otherwise the encoded length is one more than the number of prefix pairs. -/
def initializeBody : Code := .seq (read Reg.partnerLeft Reg.index Reg.value)
  (.seq (.branch (.eq Reg.value Reg.zero)
    (write Reg.lengths Reg.index Reg.one) (write Reg.lengths Reg.index Reg.zero)) (increment Reg.index))
def initializeSearch : Code := .seq (constant Reg.index 0)
  (.loop (.lt Reg.index Reg.n) initializeBody)

def copyPair : Code :=
  .seq (add Reg.rowIndex Reg.source Reg.copyIndex)
  (.seq (read Reg.rowLeft Reg.rowIndex Reg.value)
  (.seq (add Reg.rowIndex Reg.target Reg.copyIndex)
  (.seq (write Reg.rowLeft Reg.rowIndex Reg.value)
  (.seq (add Reg.rowIndex Reg.source Reg.copyIndex)
  (.seq (read Reg.rowRight Reg.rowIndex Reg.value)
  (.seq (add Reg.rowIndex Reg.target Reg.copyIndex)
  (.seq (write Reg.rowRight Reg.rowIndex Reg.value) (increment Reg.copyIndex))))))))

def discoverFresh : Code := .seq (mul Reg.source Reg.left Reg.n)
  (.seq (mul Reg.target Reg.mate Reg.n)
  (.seq (constant Reg.copyIndex 0)
  (.seq (decrement Reg.length)
  (.seq (.loop (.lt Reg.copyIndex Reg.length) copyPair)
  (.seq (add Reg.rowIndex Reg.target Reg.length)
  (.seq (write Reg.rowLeft Reg.rowIndex Reg.left)
  (.seq (write Reg.rowRight Reg.rowIndex Reg.right)
  (.seq (increment Reg.length)
  (.seq (increment Reg.length) (write Reg.lengths Reg.mate Reg.length))))))))))

def discoverMatched : Code := .seq (decrement Reg.mate)
  (.seq (read Reg.lengths Reg.mate Reg.value)
    (.branch (.eq Reg.value Reg.zero) discoverFresh skip))

def discoverReached : Code := .seq (read Reg.partnerRight Reg.right Reg.mate)
  (.branch (.eq Reg.mate Reg.zero) skip discoverMatched)

def scanBody : Code := .seq (read Reg.edgeLeft Reg.index Reg.left)
  (.seq (read Reg.edgeRight Reg.index Reg.right)
  (.seq (read Reg.lengths Reg.left Reg.length)
  (.seq (.branch (.eq Reg.length Reg.zero) skip discoverReached) (increment Reg.index))))

def sweep : Code := .seq (constant Reg.index 0) (.loop (.lt Reg.index Reg.edges) scanBody)
def search : Code := .seq initializeSearch (.seq (constant Reg.round 0)
  (.loop (.lt Reg.round Reg.n) (.seq sweep (increment Reg.round))))

def recordTerminal : Code := .seq (copy Reg.foundLeft Reg.left)
  (.seq (copy Reg.foundRight Reg.right) (increment Reg.foundRight))
def terminalReached : Code := .seq (read Reg.partnerRight Reg.right Reg.mate)
  (.branch (.eq Reg.mate Reg.zero) recordTerminal skip)
def terminalUnfound : Code := .seq (read Reg.edgeLeft Reg.index Reg.left)
  (.seq (read Reg.edgeRight Reg.index Reg.right)
  (.seq (read Reg.lengths Reg.left Reg.length)
    (.branch (.eq Reg.length Reg.zero) skip terminalReached)))
def terminalBody : Code := .seq (.branch (.eq Reg.foundRight Reg.zero) terminalUnfound skip)
  (increment Reg.index)
def terminal : Code := .seq (constant Reg.foundRight 0) (.seq (constant Reg.index 0)
  (.loop (.lt Reg.index Reg.edges) terminalBody))

/-- Pair writes use one-based partner codes, leaving zero for free vertices. -/
def pair : Code := .seq (copy Reg.value Reg.right) (.seq (increment Reg.value)
  (.seq (write Reg.partnerLeft Reg.left Reg.value)
  (.seq (copy Reg.value Reg.left) (.seq (increment Reg.value)
    (write Reg.partnerRight Reg.right Reg.value)))))
def augmentPair : Code := .seq (add Reg.rowIndex Reg.source Reg.copyIndex)
  (.seq (read Reg.rowLeft Reg.rowIndex Reg.left)
  (.seq (read Reg.rowRight Reg.rowIndex Reg.right)
    (.seq pair (increment Reg.copyIndex))))
def augment : Code := .seq (mul Reg.source Reg.foundLeft Reg.n)
  (.seq (read Reg.lengths Reg.foundLeft Reg.length)
  (.seq (decrement Reg.length) (.seq (constant Reg.copyIndex 0)
  (.seq (.loop (.lt Reg.copyIndex Reg.length) augmentPair)
  (.seq (copy Reg.left Reg.foundLeft) (.seq (copy Reg.right Reg.foundRight)
    (.seq (decrement Reg.right) pair)))))))

def phase : Code := .seq search (.seq terminal
  (.branch (.eq Reg.foundRight Reg.zero) (constant Reg.output 0) augment))
def balanced : Code := .seq (constant Reg.output 1) (.seq (constant Reg.outer 0)
  (.loop (.lt Reg.outer Reg.n)
    (.seq (.branch (.eq Reg.output Reg.zero) skip phase) (increment Reg.outer))))
def program : Code := .seq prepare
  (.branch (.eq Reg.n Reg.m) balanced (constant Reg.output 0))
def bytecode := program.program Reg.output

theorem program_capacity : program.size<1024 := by decide

end LeanTrominoes.BipartiteMatching.DenseWordRAM
