/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedAny
import LeanTrominoes.PartrecBoundedAllSpace
import LeanTrominoes.PartrecBinaryLengthSpace

/-! # Uniform binary-space certificates for bounded existential search -/

namespace Turing.PartrecToTM2.EvaluatorCodeFits
open ToPartrec

theorem isZero_bool {code : Code} {values : List Nat} {value : Bool} {budget : Nat}
    (fit : EvaluatorCodeFits code values [value.toNat] budget) :
    EvaluatorCodeFits (Code.isZero code) values [(!value).toNat] (1000*(budget+4)) := by
  have h := isZero fit
  have output : (if value.toNat = 0 then 1 else 0) = (!value).toNat := by cases value <;> rfl
  rw [output] at h
  apply h.mono
  apply isZeroCost_le_budget values value.toNat budget (budget+3)
  · exact fit.input_space.trans (by omega)
  · exact fit.output_space.trans (by omega)
  · have eq : encodedListSpace [value.toNat.pred] = 1 := by cases value <;> rfl
    rw [eq]
    omega
  · have head := encodedListSpace_singleton_headI_le values
    simp only [encodedListSpace_cons,encodedListSpace_nil] at head
    have input := fit.input_space
    omega
  · have head := encodedListSpace_singleton_headI_le values
    have next := encodeNat_succ_length_le values.headI
    simp only [encodedListSpace_cons,encodedListSpace_nil] at head
    have input := fit.input_space
    simpa only [Nat.succ_eq_add_one] using next.trans (show (Computability.encodeNat values.headI).length+1 ≤ budget+3 by omega)
  · omega
  · omega

def boundedAnyBudget (payloadSpace counterBits leafBudget : Nat) : Nat :=
  1000*(10000000*(payloadSpace+counterBits+1000*(leafBudget+4)+1)+4)

theorem boundedAny_uniform (leaf : Code) (payload : List Nat) (predicate : Nat → Bool)
    (count bits leafBudget : Nat) (countBits : (Computability.encodeNat count).length ≤ bits)
    (leafFits : ∀ i ≤ count, EvaluatorCodeFits leaf (i :: payload) [(predicate i).toNat] leafBudget) :
    EvaluatorCodeFits (Code.boundedAnyCode leaf) (count :: payload)
      [(LeanTrominoes.FiniteState.boundedAny predicate count).toNat]
      (boundedAnyBudget (encodedListSpace payload) bits leafBudget) := by
  have inner := boundedAll_uniform (leaf := Code.isZero leaf) payload (fun i => !(predicate i))
    count bits (1000*(leafBudget+4)) countBits (fun i hi => isZero_bool (leafFits i hi))
  have outer := isZero_bool inner
  simpa only [Code.boundedAnyCode,Code.allFrom_not,Bool.not_not,boundedAnyBudget] using outer

end Turing.PartrecToTM2.EvaluatorCodeFits
