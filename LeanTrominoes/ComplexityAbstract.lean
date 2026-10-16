/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.ToPartrec
import LeanWang.CoRE

/-! # Complexity notions for the formal abstracts

Mathlib supplies computability, finite-word encodings, and Turing machines;
`lean-wang` supplies co-r.e.-completeness. This file explicitly defines the
additional complexity notions used by the graph and tiling abstracts.
Turing-machine bounds use encoded length. RAM bounds below use the explicitly
stated word or structural size.
-/

namespace LeanTrominoes.ComplexityAbstract

open Computability Turing Relation

/-- Binary fields use Mathlib's little-endian natural-number encoding, with
one delimiter after each field. Signed integers use `Encodable.encode`. -/
abbrev Symbol := PartrecToTM2.Γ'
def binaryFields (fields : List ℕ) : List Symbol := PartrecToTM2.trList fields

def boolWord (b : Bool) : List Symbol := binaryFields [Encodable.encode b]

/-- A polynomial-time map is computed by an always-halting Mathlib multi-stack
Turing machine in polynomially many steps. Finite input and output alphabets
allow its internal alphabets to be restricted to finite sets as well. -/
def PolyTime {A B Γ Δ : Type} (input : A → List Γ) (output : B → List Δ)
    (f : A → B) : Prop := Nonempty (TM2ComputableInPolyTime input output f)

/-- A many-one reduction is a total polynomial-time map preserving both answers. -/
def Reduces {A B Γ Δ : Type} (input : A → List Γ) (output : B → List Δ)
    (p : A → Prop) (q : B → Prop) : Prop :=
  ∃ f : A → B, PolyTime input output f ∧ ∀ a, p a ↔ q (f a)

/-- Input symbols, the separator, and certificate bits have disjoint tags. -/
def witnessWord {A Γ : Type} (encode : A → List Γ) (input : A × List Bool) :
    List (Sum Γ (Option Bool)) :=
  (encode input.1).map Sum.inl ++ Sum.inr none :: input.2.map (fun b => Sum.inr (some b))

/-- NP membership means polynomial-length binary certificates checked by an
actual polynomial-time machine, including the cost of reading the input. -/
def InNP {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  ∃ verify : A → List Bool → Bool,
    PolyTime (witnessWord encode) boolWord (fun x => verify x.1 x.2) ∧
    ∃ bound : Polynomial ℕ, ∀ a, p a ↔ ∃ w : List Bool,
      w.length ≤ bound.eval (encode a).length ∧ verify a w = true

/-- Hardness quantifies over every finite-alphabet Mathlib input encoding.
Completeness means both membership and hardness under many-one reductions. -/
def NPHard {B Δ : Type} (encode : B → List Δ) (q : B → Prop) : Prop :=
  ∀ {A Γ : Type} [Fintype Γ] (e : Encoding A Γ) (p : A → Prop),
    InNP e.encode p → Reduces e.encode encode p q

def NPComplete {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  InNP encode p ∧ NPHard encode p

/-- Space is the total number of occupied cells on the finitely many stacks. -/
def spaceUsed (tm : FinTM2) (cfg : tm.Cfg) : ℕ :=
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.K := tm.kFin
  ∑ k, (cfg.stk k).length

/-- A polynomial-space decider halts on every encoded input and answers the
predicate correctly. Every stack alphabet is finite, and every reachable
configuration obeys the polynomial space bound. -/
structure SpaceDecider {A Γ : Type} (encode : A → List Γ) (p : A → Prop)
    extends TM2ComputableAux Γ Symbol where
  stackAlphabetFinite : ∀ k, Fintype (tm.Γ k)
  result : A → Bool
  correct : ∀ a, result a = true ↔ p a
  outputs : ∀ a, TM2Outputs tm (List.map inputAlphabet.invFun (encode a))
    (some (List.map outputAlphabet.invFun (boolWord (result a))))
  space : Polynomial ℕ
  space_le : ∀ a cfg,
    ReflTransGen (fun before after => after ∈ tm.step before)
      (initList tm (List.map inputAlphabet.invFun (encode a))) cfg →
    spaceUsed tm cfg ≤ space.eval (encode a).length

def InPSPACE {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  Nonempty (SpaceDecider encode p)

def PSPACEHard {B Δ : Type} (encode : B → List Δ) (q : B → Prop) : Prop :=
  ∀ {A Γ : Type} [Fintype Γ] (e : Encoding A Γ) (p : A → Prop),
    InPSPACE e.encode p → Reduces e.encode encode p q

def PSPACEComplete {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  InPSPACE encode p ∧ PSPACEHard encode p

/-! ## Unit-cost integer RAM

A program has finitely many registers and instructions, with unbounded integer
words and memory indexed by nonnegative integers. Each instruction costs one,
including arithmetic, indirect memory access, branches, and halting. This is
an arithmetic RAM model, not a bit-cost model. A linked cell or finite record
occupies consecutive memory words; allocation and field access must be
implemented by instructions, rather than treated as arbitrary unit-cost calls.
-/

namespace RAM

inductive Arithmetic
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

def Arithmetic.eval : Arithmetic → ℤ → ℤ → ℤ
  | .add, x, y => x+y
  | .sub, x, y => x-y
  | .mul, x, y => x*y
  | .div, x, y => x/y
  | .mod, x, y => x%y

/-- Instructions address registers statically. `load` and `store` take their
memory address from a register; negative addresses fault. Arithmetic uses
Lean's integer division and remainder, including their total zero-divisor
convention. Branch targets are instruction indices. -/
inductive Instruction (r : ℕ)
  | constant (dst : Fin r) (value : ℤ)
  | copy (dst src : Fin r)
  | arithmetic (op : Arithmetic) (dst left right : Fin r)
  | load (dst address : Fin r)
  | store (address src : Fin r)
  | jump (target : ℕ)
  | branchEq (left right : Fin r) (target : ℕ)
  | branchLt (left right : Fin r) (target : ℕ)
  | halt (result : Fin r)
  deriving DecidableEq, Repr

structure State (r : ℕ) where
  pc : ℕ
  registers : Fin r → ℤ
  memory : ℕ → ℤ

inductive Outcome (r : ℕ)
  | next (state : State r)
  | halt (value : ℤ)
  | fault

def writeRegister {r : ℕ} (s : State r) (dst : Fin r) (value : ℤ) : State r :=
  { s with pc := s.pc+1, registers := Function.update s.registers dst value }

/-- One instruction step. Falling off the program is a fault, distinct from
successful halting. No instruction can call an arbitrary Lean function. -/
def step {r : ℕ} (program : List (Instruction r)) (s : State r) : Outcome r :=
  match program[s.pc]? with
  | none => .fault
  | some (.constant dst value) => .next (writeRegister s dst value)
  | some (.copy dst src) => .next (writeRegister s dst (s.registers src))
  | some (.arithmetic op dst left right) =>
      .next (writeRegister s dst (op.eval (s.registers left) (s.registers right)))
  | some (.load dst address) =>
      if s.registers address < 0 then .fault
      else .next (writeRegister s dst (s.memory (s.registers address).toNat))
  | some (.store address src) =>
      if s.registers address < 0 then .fault
      else .next { s with
        pc := s.pc+1
        memory := Function.update s.memory (s.registers address).toNat (s.registers src) }
  | some (.jump target) => .next { s with pc := target }
  | some (.branchEq left right target) =>
      .next { s with pc := if s.registers left = s.registers right then target else s.pc+1 }
  | some (.branchLt left right target) =>
      .next { s with pc := if s.registers left < s.registers right then target else s.pc+1 }
  | some (.halt result) => .halt (s.registers result)

/-- Successful execution counts every instruction, including the final halt.
Faults have no successful execution derivation. -/
inductive Executes {r : ℕ} (program : List (Instruction r)) : State r → ℤ → ℕ → Prop
  | halt {s value} : step program s = .halt value → Executes program s value 1
  | next {s t value n} : step program s = .next t →
      Executes program t value n → Executes program s value (n+1)

/-- The input length occupies memory word zero; input words occupy addresses
1 through the length. Other memory and all registers start at zero. Input
placement is the calling convention, rather than part of the program's cost. -/
def initial {r : ℕ} (input : List ℤ) : State r :=
  { pc := 0
    registers := fun _ => 0
    memory := fun address => if address = 0 then (input.length : ℤ)
      else input[address-1]?.getD 0 }

/-- A uniform decision algorithm is one finite program for all inputs.
It must successfully halt with Boolean output within the stated number of
instructions. Program size and register count cannot depend on the input. -/
def DecidesWithin {A : Type} (encode : A → List ℤ) (p : A → Prop) (bound : A → ℕ) : Prop :=
  ∃ r, ∃ program : List (Instruction r), ∀ a, ∃ steps value,
    Executes program (initial (encode a)) value steps ∧ steps ≤ bound a ∧
      (value = 0 ∨ value = 1) ∧ (value = 1 ↔ p a)

/-- Asymptotic bounds allow a constant overhead for implementation choices.
The size function counts RAM words or structural input occurrences, as stated
for each problem; it is distinct from binary encoded length. -/
def LinearTime {A : Type} (encode : A → List ℤ) (size : A → ℕ) (p : A → Prop) : Prop :=
  ∃ C, DecidesWithin encode p (fun a => C*(size a+1))

def PolynomialTime {A : Type} (encode : A → List ℤ) (size : A → ℕ) (p : A → Prop) : Prop :=
  ∃ C k, DecidesWithin encode p (fun a => C*(size a+1)^k)

end RAM

end LeanTrominoes.ComplexityAbstract
