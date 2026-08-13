/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFuelSpace
import LeanTrominoes.PartrecMultiply

/-!
# Evaluator-space certificate for natural multiplication

The outer right-factor countdown repeatedly invokes the already fitted
fixed-width accumulator `fuelAddPreviousCode`.  Its retained product grows
monotonically, so every body call fits one envelope determined by the final
product.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def natMultiplyStepCost (values : List Nat) : Nat :=
  fuelAddPreviousCost values

theorem natMultiplyStep (values : List Nat) :
    EvaluatorCodeFits Code.natMultiplyStepCode values
      (Code.natMultiplyStepList values)
      (natMultiplyStepCost values) := by
  simpa [Code.natMultiplyStepCode,
    Code.natMultiplyStepList, natMultiplyStepCost] using
    fuelAddPrevious values

def natMultiplyBodyCost
    (remaining : Nat) (payload : List Nat) : Nat :=
  flatCountdownBodyCost Code.natMultiplyStepList
    natMultiplyStepCost remaining payload

theorem natMultiplyBody
    (remaining : Nat) (payload : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.natMultiplyStepCode)
      (remaining :: payload)
      (flatCountdownOutput Code.natMultiplyStepList
        remaining payload)
      (natMultiplyBodyCost remaining payload) := by
  simpa [natMultiplyBodyCost] using
    flatCountdownBody natMultiplyStep remaining payload

def natMultiplyInputCost (left right : Nat) : Nat :=
  let values := [left, right]
  let fourthCost := zeroCost values
  let thirdCost :=
    prependCost values [left] [0]
      (getCost 0 values) fourthCost
  let secondCost :=
    prependCost values [right] [left, 0]
      (getCost 1 values) thirdCost
  prependCost values [right] [right, left, 0]
    (getCost 1 values) secondCost

theorem natMultiplyInput (left right : Nat) :
    EvaluatorCodeFits Code.natMultiplyInputCode
      [left, right] [right, right, left, 0]
      (natMultiplyInputCost left right) := by
  let values := [left, right]
  have fourth := zero values
  have third := prepend (get 0 values) fourth
  have second := prepend (get 1 values) third
  have result := prepend (get 1 values) second
  simpa [Code.natMultiplyInputCode, natMultiplyInputCost,
    prependCost, values] using result

def NatMultiplyInvariant
    (left right remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = right ∧
      payload = [right, left, processed * left]

theorem natMultiplyInvariant_initial (left right : Nat) :
    NatMultiplyInvariant left right right [right, left, 0] := by
  exact ⟨0, by simp, by simp⟩

theorem natMultiplyInvariant_preserved
    (left right remaining : Nat) (payload : List Nat)
    (invariant :
      NatMultiplyInvariant left right (remaining + 1) payload) :
    NatMultiplyInvariant left right remaining
      (Code.natMultiplyStepList payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  simp [Code.natMultiplyStepList]
  ring

/-- A common evaluator allowance for every outer multiplication body. -/
def natMultiplyLoopCost (left right : Nat) : Nat :=
  1000000000000000000000000000000000 *
    (3 * encodedListSpace [right, left, 0] +
      encodedListSpace [right, left, right * left] + 1)

private def natMultiplyStepBudget (left right : Nat) : Nat :=
  1000000000000000000000000 *
    (3 * encodedListSpace [right, left, 0] +
      encodedListSpace [right, left, right * left] + 1)

private theorem natMultiplyStepCost_le_loop
    (left right current : Nat)
    (currentBound : current ≤ right * left)
    (nextBound : current + left ≤ right * left) :
    natMultiplyStepCost [right, left, current] ≤
      natMultiplyStepBudget left right := by
  have currentBits := encodeNat_length_mono currentBound
  have nextBits := encodeNat_length_mono nextBound
  have rightSuccessorBits := encodeNat_succ_length_le right
  have leftSuccessorBits := encodeNat_succ_length_le left
  have currentSuccessorBits := encodeNat_succ_length_le current
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [natMultiplyStepCost, fuelAddPreviousCost,
    fuelAddPreviousInputCost, fuelAddPreviousLoopCost,
    natMultiplyStepBudget,
    prependCost, getCost, dropCost, idCost,
    headCost, nilCost, zeroPrimeCost, tailCost,
    succCost, encodedListSpace_cons,
    encodedListSpace_nil, zeroBits] at *
  omega

private theorem natMultiplyBodyCost_le_loop
    (left right remaining : Nat) (payload : List Nat)
    (invariant : NatMultiplyInvariant left right remaining payload) :
    natMultiplyBodyCost remaining payload ≤
      natMultiplyLoopCost left right := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have processedBound : processed ≤ right := by omega
  have currentBound : processed * left ≤ right * left :=
    Nat.mul_le_mul_right left processedBound
  have currentBits := encodeNat_length_mono currentBound
  have remainingBound : remaining ≤ right := by omega
  have remainingBits := encodeNat_length_mono remainingBound
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [natMultiplyBodyCost, flatCountdownBodyCost,
        natMultiplyLoopCost, zeroPrimeCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits]
      omega
  | succ remaining =>
      have nextProcessedBound : processed + 1 ≤ right := by omega
      have nextBound :
          processed * left + left ≤ right * left := by
        have multiplied :=
          Nat.mul_le_mul_right left nextProcessedBound
        calc
          processed * left + left = (processed + 1) * left := by ring
          _ ≤ right * left := multiplied
      have nextBits := encodeNat_length_mono nextBound
      have inputRemainingBits := encodeNat_length_mono
        (show remaining + 1 ≤ right by omega)
      have currentRemainingBits := encodeNat_length_mono
        (show remaining ≤ right by omega)
      have stepCost := natMultiplyStepCost_le_loop
        left right (processed * left) currentBound nextBound
      simp [natMultiplyBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, natMultiplyLoopCost,
        natMultiplyStepBudget,
        Code.natMultiplyStepList,
        prependCost, idCost, headCost, nilCost,
        oneCost, zeroCost, zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] at *
      omega

def natMultiplyProjectionCost (left right : Nat) : Nat :=
  getCost 2 [right, left, right * left]

theorem natMultiplyProjection (left right : Nat) :
    EvaluatorCodeFits (Code.get 2)
      [right, left, right * left] [right * left]
      (natMultiplyProjectionCost left right) := by
  simpa [natMultiplyProjectionCost] using
    get 2 [right, left, right * left]

def natMultiplyCost (left right : Nat) : Nat :=
  natMultiplyProjectionCost left right +
    natMultiplyLoopCost left right +
      natMultiplyInputCost left right

theorem natMultiply (left right : Nat) :
    EvaluatorCodeFits Code.natMultiplyCode
      [left, right] [left * right]
      (natMultiplyCost left right) := by
  have finalPayload :
      (Code.natMultiplyStepList^[right]) [right, left, 0] =
        [right, left, right * left] := by
    rw [Code.natMultiplyStepList_iterate]
    simp
  have loopThenProjection :
      EvaluatorCodeFits
        ((Code.get 2).comp
          (Code.flatIterate Code.natMultiplyStepCode))
        [right, right, left, 0] [right * left]
        (natMultiplyProjectionCost left right +
          natMultiplyLoopCost left right) := {
    input_space := by
      simp [natMultiplyLoopCost]
      omega
    output_space := by
      exact (natMultiplyProjection left right).output_space.trans
        (Nat.le_add_right _ _)
    call continuation bound budget after := by
      have projectionCall :=
        (natMultiplyProjection left right).call continuation bound
          (by omega) after
      have flatCall :
          EvaluatorCallFits
            (Code.flatIterate Code.natMultiplyStepCode)
            (.comp (Code.get 2) continuation)
            [right, right, left, 0] bound := by
        apply
          EvaluatorCallFits.flatIterate_of_code_fits_invariant
            (bodyCost := natMultiplyBodyCost)
            (invariant := NatMultiplyInvariant left right)
        · exact natMultiplyBody
        · exact natMultiplyInvariant_initial left right
        · exact natMultiplyInvariant_preserved left right
        · intro remaining payload invariant
          have bodyCost := natMultiplyBodyCost_le_loop
            left right remaining payload invariant
          simp only [continuationSpace_comp]
          omega
        · rw [finalPayload]
          apply EvaluatorExecutionFits.ret_comp
          · simp only [continuationSpace_comp]
            have projectionInput :=
              (natMultiplyProjection left right).input_space
            omega
          · exact projectionCall
      exact EvaluatorCallFits.comp flatCall
    }
  have result := comp loopThenProjection
    (natMultiplyInput left right)
  simpa [Code.natMultiplyCode, natMultiplyCost,
    Nat.add_assoc, Nat.mul_comm] using result

set_option maxHeartbeats 1000000 in
theorem natMultiplyCost_le_linear (left right : Nat) :
    natMultiplyCost left right ≤
      1000000000000000000000000000000000000 *
        (encodedListSpace
          [16 * (left + right + left * right + 10) + 100] + 1) := by
  let limit := 16 * (left + right + left * right + 10) + 100
  have leftBound : left ≤ limit := by simp only [limit]; omega
  have rightBound : right ≤ limit := by simp only [limit]; omega
  have productBound : left * right ≤ limit := by
    simp only [limit]
    omega
  have leftBits := encodeNat_length_mono leftBound
  have rightBits := encodeNat_length_mono rightBound
  have productBits := encodeNat_length_mono productBound
  have leftSuccBits := encodeNat_length_mono
    (show left + 1 ≤ limit by simp only [limit]; omega)
  have rightSuccBits := encodeNat_length_mono
    (show right + 1 ≤ limit by simp only [limit]; omega)
  have productSuccBits := encodeNat_length_mono
    (show left * right + 1 ≤ limit by simp only [limit]; omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have productComm : right * left = left * right := by
    exact Nat.mul_comm right left
  simp [natMultiplyCost, natMultiplyInputCost,
    natMultiplyProjectionCost, natMultiplyLoopCost,
    prependCost, getCost, dropCost, idCost,
    headCost, nilCost, zeroCost, zeroPrimeCost,
    tailCost, succCost, encodedListSpace_cons,
    encodedListSpace_nil, zeroBits, limit] at *
  rw [productComm] at *
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
