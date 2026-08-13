/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecSubtractSpace

/-!
# Evaluator-space certificate for natural equality

The certificate composes two fitted truncated subtractions, zero tests, and
one short-circuiting conjunction.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def swapPairCost (left right : Nat) : Nat :=
  prependCost [left, right] [right] [left]
    (getCost 1 [left, right])
    (getCost 0 [left, right])

theorem swapPair (left right : Nat) :
    EvaluatorCodeFits Code.swapPairCode
      [left, right] [right, left]
      (swapPairCost left right) := by
  simpa [Code.swapPairCode, swapPairCost,
    prependCost] using
    prepend (get 1 [left, right])
      (get 0 [left, right])

def reverseSubtractCost (left right : Nat) : Nat :=
  subtractCost right left + swapPairCost left right

theorem reverseSubtract (left right : Nat) :
    EvaluatorCodeFits Code.reverseSubtractCode
      [left, right] [right - left]
      (reverseSubtractCost left right) := by
  simpa [Code.reverseSubtractCode,
    reverseSubtractCost] using
    comp (subtract right left) (swapPair left right)

def forwardZeroCost (left right : Nat) : Nat :=
  isZeroCost [left, right] (left - right)
    (subtractCost left right)

theorem forwardZero (left right : Nat) :
    EvaluatorCodeFits (Code.isZero Code.subtractCode)
      [left, right]
      [if left - right = 0 then 1 else 0]
      (forwardZeroCost left right) := by
  simpa [forwardZeroCost] using
    isZero (subtract left right)

def reverseZeroCost (left right : Nat) : Nat :=
  isZeroCost [left, right] (right - left)
    (reverseSubtractCost left right)

theorem reverseZero (left right : Nat) :
    EvaluatorCodeFits
      (Code.isZero Code.reverseSubtractCode)
      [left, right]
      [if right - left = 0 then 1 else 0]
      (reverseZeroCost left right) := by
  simpa [reverseZeroCost] using
    isZero (reverseSubtract left right)

def natEqCost (left right : Nat) : Nat :=
  let forward := if left - right = 0 then 1 else 0
  let reverse := if right - left = 0 then 1 else 0
  boolAndCost [left, right] forward reverse
    (forwardZeroCost left right)
    (reverseZeroCost left right)

theorem natEq (left right : Nat) :
    EvaluatorCodeFits Code.natEqCode
      [left, right]
      [if left = right then 1 else 0]
      (natEqCost left right) := by
  have combined :=
    boolAnd (forwardZero left right)
      (reverseZero left right)
  by_cases equal : left = right
  · subst right
    simpa [Code.natEqCode, natEqCost] using combined
  · rcases lt_or_gt_of_ne equal with less | greater
    · have forward : left - right = 0 := by omega
      have reverse : right - left ≠ 0 := by omega
      simpa [Code.natEqCode, natEqCost,
        equal, forward, reverse] using combined
    · have forward : left - right ≠ 0 := by omega
      simpa [Code.natEqCode, natEqCost,
        equal, forward] using combined

set_option maxHeartbeats 800000 in
theorem natEqCost_le_linear (left right : Nat) :
    natEqCost left right ≤
      10000000000 *
        (encodedListSpace [2 * (left + right) + 4] + 1) := by
  let limit := 2 * (left + right) + 4
  have leftBound : left ≤ limit := by
    simp only [limit]
    omega
  have rightBound : right ≤ limit := by
    simp only [limit]
    omega
  have forwardBound : left - right ≤ limit :=
    (Nat.sub_le left right).trans leftBound
  have reverseBound : right - left ≤ limit :=
    (Nat.sub_le right left).trans rightBound
  have leftBits := encodeNat_length_mono leftBound
  have rightBits := encodeNat_length_mono rightBound
  have forwardBits := encodeNat_length_mono forwardBound
  have reverseBits := encodeNat_length_mono reverseBound
  have forwardPredBits :=
    encodeNat_length_mono
      ((Nat.pred_le (left - right)).trans forwardBound)
  have reversePredBits :=
    encodeNat_length_mono
      ((Nat.pred_le (right - left)).trans reverseBound)
  have leftSuccBits :=
    encodeNat_length_mono
      (show left + 1 ≤ limit by
        simp only [limit]
        omega)
  have rightSuccBits :=
    encodeNat_length_mono
      (show right + 1 ≤ limit by
        simp only [limit]
        omega)
  have forwardSuccBits :=
    encodeNat_length_mono
      (show left - right + 1 ≤ limit by
        simp only [limit]
        omega)
  have reverseSuccBits :=
    encodeNat_length_mono
      (show right - left + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  by_cases forwardZero : left - right = 0 <;>
    by_cases reverseZero : right - left = 0 <;>
    simp [natEqCost, forwardZeroCost, reverseZeroCost,
      reverseSubtractCost, swapPairCost, isZeroCost,
      boolAndCost, normalizeBoolCost,
      subtractCost, subtractInputCost, subtractLoopCost,
      branchZeroZeroCost, branchZeroSuccCost,
      branchZeroTestCost, prependCost, getCost, dropCost,
      headCost, idCost, nilCost, zeroCost, oneCost,
      tailCost, zeroPrimeCost, succCost,
      forwardZero, reverseZero,
      encodedListSpace_cons, encodedListSpace_nil,
      limit, zeroBits, oneBits] at * <;>
    omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
