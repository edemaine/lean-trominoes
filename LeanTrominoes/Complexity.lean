import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Computable

/-!
# Space-bounded decision problems

Mathlib supplies finite multi-stack Turing machines and polynomial-time
computation, but not a packaged PSPACE predicate. This file adds only the
definitions needed to state the 1.5D half of Theorem 5.2.
-/

noncomputable section

open scoped BigOperators

namespace LeanTrominoes.Complexity

open Computability
open Relation
open Turing

/-- A binary finite encoding induced by a `Primcodable` encoding. -/
def primcodableFinEncoding (α : Type*) [Primcodable α] : FinEncoding α where
  Γ := Bool
  encode value := encodeNat (Encodable.encode value)
  decode bits := Encodable.decode (decodeNat bits)
  decode_encode value := by simp
  ΓFin := inferInstance

/-- Space occupied by a TM2 configuration, measured as the total number of
cells across its finitely many stacks. Finite control is constant-size. -/
def configurationSpace (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.K := tm.kFin
  ∑ stack, (cfg.stk stack).length

/-- A total decider for `language` whose reachable configurations use space
bounded by a polynomial in the encoded input length. All stack alphabets are
required to be finite, so one stack cell contains only constant information. -/
structure DeciderInPolySpace {α : Type} (encoding : FinEncoding α)
    (language : α → Prop) extends TM2ComputableAux encoding.Γ Bool where
  stackAlphabetFinite : ∀ stack, Fintype (tm.Γ stack)
  result : α → Bool
  correct : ∀ input, result input = true ↔ language input
  outputs :
    ∀ input,
      TM2Outputs tm
        (List.map inputAlphabet.invFun (encoding.encode input))
        (some (List.map outputAlphabet.invFun [result input]))
  space : Polynomial Nat
  space_le :
    ∀ input cfg,
      ReflTransGen (fun before after => after ∈ tm.step before)
          (initList tm (List.map inputAlphabet.invFun (encoding.encode input))) cfg →
        configurationSpace tm cfg ≤ space.eval (encoding.encode input).length

/-- Membership of a decision predicate in PSPACE, relative to a finite input
encoding. -/
def InPSPACE {α : Type} (encoding : FinEncoding α) (language : α → Prop) : Prop :=
  Nonempty (DeciderInPolySpace encoding language)

/-- Polynomial-time many-one reducibility between encoded decision predicates. -/
def PolyTimeManyOneReducible {α β : Type}
    (encodingA : FinEncoding α) (encodingB : FinEncoding β)
    (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ reduce : α → β,
    Nonempty (TM2ComputableInPolyTime encodingA.encode encodingB.encode reduce) ∧
      ∀ input, p input ↔ q (reduce input)

/-- Every PSPACE predicate polynomial-time many-one reduces to `language`. -/
def PSPACEHard {β : Type} (encoding : FinEncoding β) (language : β → Prop) : Prop :=
  ∀ {α : Type} (sourceEncoding : FinEncoding α) (source : α → Prop),
    InPSPACE sourceEncoding source →
      PolyTimeManyOneReducible sourceEncoding encoding source language

/-- A predicate is PSPACE-complete when it belongs to PSPACE and is
PSPACE-hard under polynomial-time many-one reductions. -/
def PSPACEComplete {α : Type} (encoding : FinEncoding α) (language : α → Prop) : Prop :=
  InPSPACE encoding language ∧ PSPACEHard encoding language

end LeanTrominoes.Complexity
