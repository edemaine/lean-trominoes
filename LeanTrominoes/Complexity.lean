/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetPolyTime
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.ToPartrec

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

/-- Translate a binary symbol to the corresponding symbol of Mathlib's
four-symbol partial-recursive evaluator alphabet. -/
def partrecBit : Bool → Turing.PartrecToTM2.Γ'
  | false => .bit0
  | true => .bit1

/-- Read a binary symbol from the evaluator alphabet.  The arbitrary values
on delimiter symbols are irrelevant after the final delimiter is removed. -/
def partrecUnbit : Turing.PartrecToTM2.Γ' → Bool
  | .bit0 => false
  | .bit1 => true
  | .cons => false
  | .consₗ => false

@[simp]
theorem partrecUnbit_partrecBit (bit : Bool) :
    partrecUnbit (partrecBit bit) = bit := by
  cases bit <;> rfl

theorem partrec_trPosNum_eq_map_encodePosNum (number : PosNum) :
    Turing.PartrecToTM2.trPosNum number =
      (encodePosNum number).map partrecBit := by
  induction number with
  | one => rfl
  | bit0 number ih =>
      simp [Turing.PartrecToTM2.trPosNum, encodePosNum, ih, partrecBit]
  | bit1 number ih =>
      simp [Turing.PartrecToTM2.trPosNum, encodePosNum, ih, partrecBit]

theorem partrec_trNat_eq_map_encodeNat (number : Nat) :
    Turing.PartrecToTM2.trNat number =
      (encodeNat number).map partrecBit := by
  rw [← Num.to_of_nat number]
  generalize (number : Num) = encoded
  cases encoded with
  | zero => rfl
  | pos positive =>
      simpa [Turing.PartrecToTM2.trNat,
        Turing.PartrecToTM2.trNum, encodeNat, encodeNum] using
        partrec_trPosNum_eq_map_encodePosNum positive

@[simp]
theorem partrec_trNat_length (number : Nat) :
    (Turing.PartrecToTM2.trNat number).length =
      (encodeNat number).length := by
  rw [partrec_trNat_eq_map_encodeNat, List.length_map]

/-- A binary finite encoding induced by a `Primcodable` encoding, in the
native input format of Mathlib's partial-recursive evaluator.  It is the
ordinary little-endian binary encoding followed by one list delimiter. -/
def primcodableFinEncoding (α : Type*) [Primcodable α] : FinEncoding α where
  Γ := Turing.PartrecToTM2.Γ'
  encode value :=
    Turing.PartrecToTM2.trList [Encodable.encode value]
  decode symbols :=
    Encodable.decode
      (decodeNat (symbols.dropLast.map partrecUnbit))
  decode_encode value := by
    simp [partrec_trNat_eq_map_encodeNat, Function.comp_def]
  ΓFin := inferInstance

@[simp]
theorem primcodableFinEncoding_encode_length
    (α : Type*) [Primcodable α] (value : α) :
    ((primcodableFinEncoding α).encode value).length =
      (encodeNat (Encodable.encode value)).length + 1 := by
  simp [primcodableFinEncoding, Turing.PartrecToTM2.trList]

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
    (language : α → Prop) extends
      TM2ComputableAux encoding.Γ Turing.PartrecToTM2.Γ' where
  stackAlphabetFinite : ∀ stack, Fintype (tm.Γ stack)
  result : α → Bool
  correct : ∀ input, result input = true ↔ language input
  outputs :
    ∀ input,
      TM2Outputs tm
        (List.map inputAlphabet.invFun (encoding.encode input))
        (some (List.map outputAlphabet.invFun
          ((primcodableFinEncoding Bool).encode (result input))))
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

/-- Polynomial-time many-one reducibility between encoded decision predicates,
with finite alphabets on every stack of the reduction machine. -/
def PolyTimeManyOneReducible {α β : Type}
    (encodingA : FinEncoding α) (encodingB : FinEncoding β)
    (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ reduce : α → β,
    Nonempty (FiniteAlphabetComputableInPolyTime encodingA.encode encodingB.encode reduce) ∧
      ∀ input, p input ↔ q (reduce input)

/-- Restrict a Mathlib reduction machine to finite stack alphabets before
packaging it. The reduction function and polynomial time bound are preserved. -/
theorem PolyTimeManyOneReducible.of_computableInPolyTime {α β : Type}
    {encodingA : FinEncoding α} {encodingB : FinEncoding β}
    {p : α → Prop} {q : β → Prop}
    (reduce : α → β)
    (compiler : Nonempty
      (TM2ComputableInPolyTime encodingA.encode encodingB.encode reduce))
    (correct : ∀ input, p input ↔ q (reduce input)) :
    PolyTimeManyOneReducible encodingA encodingB p q :=
  ⟨reduce, compiler.map FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime, correct⟩

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
