/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecNatCompare
import LeanTrominoes.PartrecSubtractSpace
import LeanTrominoes.PartrecBooleanSpace

/-!
# Evaluator-space certificates for natural comparisons

The fitted strict comparison composes argument reordering, truncated
subtraction, and Boolean normalization.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def natLtArgumentsCost (left right : Nat) : Nat :=
  prependCost [left, right] [right] [left]
    (getCost 1 [left, right])
    (getCost 0 [left, right])

theorem natLtArguments (left right : Nat) :
    EvaluatorCodeFits Code.natLtArgumentsCode
      [left, right] [right, left]
      (natLtArgumentsCost left right) := by
  simpa [Code.natLtArgumentsCode,
    natLtArgumentsCost, prependCost] using
    prepend (get 1 [left, right])
      (get 0 [left, right])

def natLtDifferenceCost (left right : Nat) : Nat :=
  subtractCost right left +
    natLtArgumentsCost left right

theorem natLtDifference (left right : Nat) :
    EvaluatorCodeFits Code.natLtDifferenceCode
      [left, right] [right - left]
      (natLtDifferenceCost left right) := by
  simpa [Code.natLtDifferenceCode,
    natLtDifferenceCost] using
    comp (subtract right left)
      (natLtArguments left right)

def natLtCost (left right : Nat) : Nat :=
  normalizeBoolCost [left, right] (right - left)
    (natLtDifferenceCost left right)

theorem natLt (left right : Nat) :
    EvaluatorCodeFits Code.natLtCode
      [left, right]
      [if left < right then 1 else 0]
      (natLtCost left right) := by
  have normalized :=
    normalizeBool (natLtDifference left right)
  have semantic :
      (if right - left = 0 then 0 else 1) =
        (if left < right then 1 else 0) := by
    split <;> split <;> omega
  rw [semantic] at normalized
  simpa [Code.natLtCode, natLtCost] using normalized

set_option maxHeartbeats 800000 in
theorem natLtCost_le_linear (left right : Nat) :
    natLtCost left right ≤
      1000000000 *
        (encodedListSpace [2 * (left + right) + 4] + 1) := by
  let limit := 2 * (left + right) + 4
  have leftBound : left ≤ limit := by
    simp only [limit]
    omega
  have rightBound : right ≤ limit := by
    simp only [limit]
    omega
  have differenceBound : right - left ≤ limit :=
    (Nat.sub_le right left).trans rightBound
  have leftBits := encodeNat_length_mono leftBound
  have rightBits := encodeNat_length_mono rightBound
  have differenceBits :=
    encodeNat_length_mono differenceBound
  have differencePredBits :=
    encodeNat_length_mono
      ((Nat.pred_le (right - left)).trans differenceBound)
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
  have differenceSuccBits :=
    encodeNat_length_mono
      (show right - left + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  by_cases differenceZero : right - left = 0 <;>
    simp [natLtCost, natLtDifferenceCost,
      natLtArgumentsCost, normalizeBoolCost,
      subtractCost, subtractInputCost, subtractLoopCost,
      branchZeroZeroCost, branchZeroSuccCost,
      branchZeroTestCost, prependCost, getCost, dropCost,
      headCost, idCost, nilCost, zeroCost, oneCost,
      tailCost, zeroPrimeCost, succCost, differenceZero,
      encodedListSpace_cons, encodedListSpace_nil,
      limit, zeroBits, oneBits] at * <;>
    omega

def natPositiveCost (number : Nat) : Nat :=
  normalizeBoolCost [number] number
    (headCost [number])

theorem natPositive (number : Nat) :
    EvaluatorCodeFits Code.natPositiveCode [number]
      [if 0 < number then 1 else 0]
      (natPositiveCost number) := by
  have normalized := normalizeBool (head [number])
  by_cases zero : number = 0
  · have notPositive : ¬0 < number := by omega
    simpa [Code.natPositiveCode,
      natPositiveCost, zero, notPositive] using normalized
  · have positive : 0 < number := Nat.pos_of_ne_zero zero
    simpa [Code.natPositiveCode,
      natPositiveCost, zero, positive] using normalized

end EvaluatorCodeFits

end PartrecToTM2
end Turing
