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
additional notions used by the graph and tiling abstracts:

* polynomial-time maps and many-one reductions;
* NP membership, hardness, and completeness;
* PSPACE membership, hardness, and completeness;
* a bounded-word RAM and instruction-count bounds, needed to express
  running times such as O(n²) in RAM instructions. `RAM.DecidesWithin` defines
  a uniform program with an instruction budget; `RAM.LinearTime` and
  `RAM.PolynomialTime` specify the logarithmic word-size requirement.

Turing-machine bounds use encoded length. RAM bounds below use the explicitly
stated word or structural size.
-/

namespace LeanTrominoes.ComplexityAbstract

/-! ## Encodings and polynomial-time reductions -/

/-- Binary fields use Mathlib's little-endian natural-number encoding, with
one delimiter after each field. Signed integers use `Encodable.encode`. -/
abbrev Symbol := Turing.PartrecToTM2.Γ'
def binaryFields (fields : List ℕ) : List Symbol := Turing.PartrecToTM2.trList fields

def boolWord (b : Bool) : List Symbol := binaryFields [Encodable.encode b]

/-- A polynomial-time map is computed by an always-halting Mathlib multi-stack
Turing machine in polynomially many steps. Finite input and output alphabets
allow its internal alphabets to be restricted to finite sets as well. -/
def PolyTime {A B Γ Δ : Type} (input : A → List Γ) (output : B → List Δ)
    (f : A → B) : Prop := Nonempty (Turing.TM2ComputableInPolyTime input output f)

/-- A many-one reduction is a total polynomial-time map preserving both answers. -/
def Reduces {A B Γ Δ : Type} (input : A → List Γ) (output : B → List Δ)
    (p : A → Prop) (q : B → Prop) : Prop :=
  ∃ f : A → B, PolyTime input output f ∧ ∀ a, p a ↔ q (f a)

/-! ## NP -/

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
  ∀ {A Γ : Type} [Fintype Γ] (e : Computability.Encoding A Γ) (p : A → Prop),
    InNP e.encode p → Reduces e.encode encode p q

def NPComplete {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  InNP encode p ∧ NPHard encode p

/-! ## PSPACE -/

/-- Space is the total number of occupied cells on the finitely many stacks. -/
def spaceUsed (tm : Turing.FinTM2) (cfg : tm.Cfg) : ℕ :=
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.K := tm.kFin
  ∑ k, (cfg.stk k).length

/-- A polynomial-space decider halts on every encoded input and answers the
predicate correctly. Every stack alphabet is finite, and every reachable
configuration obeys the polynomial space bound. -/
structure SpaceDecider {A Γ : Type} (encode : A → List Γ) (p : A → Prop)
    extends Turing.TM2ComputableAux Γ Symbol where
  stackAlphabetFinite : ∀ k, Fintype (tm.Γ k)
  result : A → Bool
  correct : ∀ a, result a = true ↔ p a
  outputs : ∀ a, Turing.TM2Outputs tm (List.map inputAlphabet.invFun (encode a))
    (some (List.map outputAlphabet.invFun (boolWord (result a))))
  space : Polynomial ℕ
  space_le : ∀ a cfg,
    Relation.ReflTransGen (fun before after => after ∈ tm.step before)
      (Turing.initList tm (List.map inputAlphabet.invFun (encode a))) cfg →
    spaceUsed tm cfg ≤ space.eval (encode a).length

def InPSPACE {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  Nonempty (SpaceDecider encode p)

def PSPACEHard {B Δ : Type} (encode : B → List Δ) (q : B → Prop) : Prop :=
  ∀ {A Γ : Type} [Fintype Γ] (e : Computability.Encoding A Γ) (p : A → Prop),
    InPSPACE e.encode p → Reduces e.encode encode p q

def PSPACEComplete {A Γ : Type} (encode : A → List Γ) (p : A → Prop) : Prop :=
  InPSPACE encode p ∧ PSPACEHard encode p

/-! ## Bounded-word RAM

A program has finitely many registers and instructions. At word size w ≥ 1,
registers and memory contain signed w-bit integers, and addresses are unsigned
w-bit integers. Each instruction costs one. Overflow and out-of-range addresses
fault; successful runs must therefore establish all word bounds. Integer-valued
functions represent the finite stores mathematically, without granting access
to larger integers or addresses. Multiplication and division are unit-cost
operations on words; an overflowing result is rejected.

Memory allocation reserves fresh blocks and initializes their cells using
ordinary instructions. Indexed array access adds an index to a block pointer.
Space usage is the high-water mark, including storage no longer used; its bound
ensures pointers fit in words even without a separate space-complexity claim.
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
memory address from a nonnegative register value; negative addresses fault. Arithmetic uses
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

/-- Signed two's-complement range, with a positive word size. -/
def Fits (w : ℕ) (value : ℤ) : Prop :=
  0 < w ∧ -(2^(w-1) : ℤ) ≤ value ∧ value < (2^(w-1) : ℤ)

instance (w : ℕ) (value : ℤ) : Decidable (Fits w value) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

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

/-- Advancing control must also fit the unsigned address space. -/
def next {r : ℕ} (w : ℕ) (s : State r) : Outcome r :=
  if s.pc < 2^w then .next s else .fault

/-- Every register write checks the signed word range. -/
def write {r : ℕ} (w : ℕ) (s : State r) (dst : Fin r) (value : ℤ) : Outcome r :=
  if Fits w value then next w (writeRegister s dst value) else .fault

/-- One bounded-word instruction step. Falling off the program, arithmetic
overflow, and invalid addresses fault. Halting also checks the output word. -/
def step {r : ℕ} (w : ℕ) (program : List (Instruction r)) (s : State r) : Outcome r :=
  if s.pc ≥ 2^w then .fault else
  match program[s.pc]? with
  | none => .fault
  | some (.constant dst value) => write w s dst value
  | some (.copy dst src) => write w s dst (s.registers src)
  | some (.arithmetic op dst left right) =>
      write w s dst (op.eval (s.registers left) (s.registers right))
  | some (.load dst address) =>
      if s.registers address < 0 ∨ s.registers address ≥ (2^w : ℕ) then .fault
      else write w s dst (s.memory (s.registers address).toNat)
  | some (.store address src) =>
      if s.registers address < 0 ∨ s.registers address ≥ (2^w : ℕ) ∨ ¬ Fits w (s.registers src) then .fault
      else next w { s with
        pc := s.pc+1
        memory := Function.update s.memory (s.registers address).toNat (s.registers src) }
  | some (.jump target) => next w { s with pc := target }
  | some (.branchEq left right target) =>
      next w { s with pc := if s.registers left = s.registers right then target else s.pc+1 }
  | some (.branchLt left right target) =>
      next w { s with pc := if s.registers left < s.registers right then target else s.pc+1 }
  | some (.halt result) => if Fits w (s.registers result) then .halt (s.registers result) else .fault

/-- Successful execution counts every instruction, including the final halt.
Faults have no successful execution derivation. -/
inductive Executes {r : ℕ} (w : ℕ) (program : List (Instruction r)) : State r → ℤ → ℕ → Prop
  | halt {s value} : step w program s = .halt value → Executes w program s value 1
  | next {s t value n} : step w program s = .next t →
      Executes w program t value n → Executes w program s value (n+1)

/-- The input length occupies memory word zero; input words occupy addresses
1 through the length. Other memory and all registers start at zero. Input
placement is the calling convention, rather than part of the program's cost. -/
def initial {r : ℕ} (input : List ℤ) : State r :=
  { pc := 0
    registers := fun _ => 0
    memory := fun address => if address = 0 then (input.length : ℤ)
      else input[address-1]?.getD 0 }

/-- Input words and the length header must fit the signed word range. The
length condition also ensures the input addresses fit the address space. -/
def InputFits (w : ℕ) (input : List ℤ) : Prop :=
  Fits w input.length ∧ ∀ value ∈ input, Fits w value

/-- A uniform decision algorithm uses the same finite program for all inputs
and word sizes. At every size above the stated threshold, it must halt correctly
within the instruction budget whenever the input words fit. Faulting executions
do not satisfy this definition. -/
def DecidesWithin {A : Type} (encode : A → List ℤ) (p : A → Prop)
    (bound requiredBits : A → ℕ) : Prop :=
  ∃ r, ∃ program : List (Instruction r), ∀ a w, requiredBits a ≤ w → InputFits w (encode a) →
    ∃ steps value, Executes w program (initial (encode a)) value steps ∧ steps ≤ bound a ∧
      (value = 0 ∨ value = 1) ∧ (value = 1 ↔ p a)

/-- Linear and polynomial time require only a constant multiple of log₂(size+2)
bits, and hold for every larger word size accommodating the input integers.
The size counts RAM input words or the explicitly stated structural size. -/
def LinearTime {A : Type} (encode : A → List ℤ) (size : A → ℕ) (p : A → Prop) : Prop :=
  ∃ C k, DecidesWithin encode p (fun a => C*(size a+1))
    (fun a => k*Nat.log2 (size a+2)+2)

def PolynomialTime {A : Type} (encode : A → List ℤ) (size : A → ℕ) (p : A → Prop) : Prop :=
  ∃ C exponent k, DecidesWithin encode p (fun a => C*(size a+1)^exponent)
    (fun a => k*Nat.log2 (size a+2)+2)

end RAM

end LeanTrominoes.ComplexityAbstract
