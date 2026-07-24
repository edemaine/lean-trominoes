import LeanTrominoes.PartrecUnpair
import LeanTrominoes.PartrecSqrtSpace
import LeanTrominoes.PartrecSubtractSpace

/-!
# Evaluator-space certificate for standard unpairing

The certificate composes the fitted square-root state with three fitted
truncated subtractions: shell remainder, branch test, and the lower-edge
coordinate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def unpairRemainderArgumentsCost (values : List Nat) : Nat :=
  prependCost values [values[1]?.getD 0]
    [values[0]?.getD 0]
    (getCost 1 values) (getCost 0 values)

theorem unpairRemainderArguments (values : List Nat) :
    EvaluatorCodeFits Code.unpairRemainderArgumentsCode values
      [values[1]?.getD 0, values[0]?.getD 0]
      (unpairRemainderArgumentsCost values) := by
  simpa [Code.unpairRemainderArgumentsCode,
    unpairRemainderArgumentsCost, prependCost] using
    prepend (get 1 values) (get 0 values)

def unpairRemainderCost (distance gap root : Nat) : Nat :=
  subtractCost gap distance +
    unpairRemainderArgumentsCost [distance, gap, root]

theorem unpairRemainder
    (distance gap root : Nat) :
    EvaluatorCodeFits
      (Code.subtractCode.comp
        Code.unpairRemainderArgumentsCode)
      [distance, gap, root] [gap - distance]
      (unpairRemainderCost distance gap root) := by
  simpa [unpairRemainderCost] using
    comp (subtract gap distance)
      (unpairRemainderArguments [distance, gap, root])

def unpairRemainderStateCost
    (distance gap root : Nat) : Nat :=
  prependCost [distance, gap, root]
    [gap - distance] [root]
    (unpairRemainderCost distance gap root)
    (getCost 2 [distance, gap, root])

theorem unpairRemainderState (number : Nat) :
    let root := Nat.sqrt number
    let distance :=
      (root + 1) * (root + 1) - number
    let gap := 2 * root + 1
    EvaluatorCodeFits Code.unpairRemainderStateCode
      [distance, gap, root]
      [number - root * root, root]
      (unpairRemainderStateCost distance gap root) := by
  let root := Nat.sqrt number
  let distance :=
    (root + 1) * (root + 1) - number
  let gap := 2 * root + 1
  have remainder :=
    unpairRemainder distance gap root
  have result :=
    prepend remainder (get 2 [distance, gap, root])
  have remainderEq :
      gap - distance = number - root * root := by
    simpa [gap, distance, root] using
      Code.sqrtGap_sub_distance number
  rw [remainderEq] at result
  simpa [Code.unpairRemainderStateCode,
    unpairRemainderStateCost, prependCost,
    root, distance, gap, remainderEq] using result

def unpairStateCost (number : Nat) : Nat :=
  let root := Nat.sqrt number
  let distance :=
    (root + 1) * (root + 1) - number
  let gap := 2 * root + 1
  unpairRemainderStateCost distance gap root +
    sqrtStateCost number

theorem unpairState (number : Nat) :
    EvaluatorCodeFits Code.unpairStateCode [number]
      [number - Nat.sqrt number * Nat.sqrt number,
        Nat.sqrt number]
      (unpairStateCost number) := by
  have remainderState := unpairRemainderState number
  have squareRootState := sqrtState number
  have result := comp remainderState squareRootState
  simpa [Code.unpairStateCode, unpairStateCost] using result

def unpairTestArgumentsCost (values : List Nat) : Nat :=
  prependCost values [values[1]?.getD 0]
    [values[0]?.getD 0]
    (getCost 1 values) (getCost 0 values)

theorem unpairTestArguments (values : List Nat) :
    EvaluatorCodeFits Code.unpairTestArgumentsCode values
      [values[1]?.getD 0, values[0]?.getD 0]
      (unpairTestArgumentsCost values) := by
  simpa [Code.unpairTestArgumentsCode,
    unpairTestArgumentsCost, prependCost] using
    prepend (get 1 values) (get 0 values)

def unpairTestCost (remainder root : Nat) : Nat :=
  subtractCost root remainder +
    unpairTestArgumentsCost [remainder, root]

theorem unpairTest (remainder root : Nat) :
    EvaluatorCodeFits Code.unpairTestCode
      [remainder, root] [root - remainder]
      (unpairTestCost remainder root) := by
  simpa [Code.unpairTestCode, unpairTestCost] using
    comp (subtract root remainder)
      (unpairTestArguments [remainder, root])

def unpairRightArgumentsCost (values : List Nat) : Nat :=
  prependCost values [values[0]?.getD 0]
    [values[1]?.getD 0]
    (getCost 0 values) (getCost 1 values)

theorem unpairRightArguments (values : List Nat) :
    EvaluatorCodeFits Code.unpairRightArgumentsCode values
      [values[0]?.getD 0, values[1]?.getD 0]
      (unpairRightArgumentsCost values) := by
  simpa [Code.unpairRightArgumentsCode,
    unpairRightArgumentsCost, prependCost] using
    prepend (get 0 values) (get 1 values)

def unpairRightCost (remainder root : Nat) : Nat :=
  subtractCost remainder root +
    unpairRightArgumentsCost [remainder, root]

theorem unpairRight (remainder root : Nat) :
    EvaluatorCodeFits
      (Code.subtractCode.comp
        Code.unpairRightArgumentsCode)
      [remainder, root] [remainder - root]
      (unpairRightCost remainder root) := by
  simpa [unpairRightCost] using
    comp (subtract remainder root)
      (unpairRightArguments [remainder, root])

def unpairLowerCost (remainder root : Nat) : Nat :=
  prependCost [remainder, root] [root]
    [remainder - root]
    (getCost 1 [remainder, root])
    (unpairRightCost remainder root)

theorem unpairLower (remainder root : Nat) :
    EvaluatorCodeFits Code.unpairLowerCode
      [remainder, root] [root, remainder - root]
      (unpairLowerCost remainder root) := by
  simpa [Code.unpairLowerCode, unpairLowerCost,
    prependCost] using
    prepend (get 1 [remainder, root])
      (unpairRight remainder root)

def unpairFinalCost (remainder root : Nat) : Nat :=
  if remainder < root then
    branchZeroSuccCost [remainder, root] [remainder, root]
      (root - remainder)
      (unpairTestCost remainder root)
      (idCost [remainder, root])
  else
    branchZeroZeroCost [remainder, root]
      [root, remainder - root]
      (root - remainder)
      (unpairTestCost remainder root)
      (unpairLowerCost remainder root)

theorem unpairFinal (remainder root : Nat) :
    EvaluatorCodeFits Code.unpairFinalCode
      [remainder, root]
      (if remainder < root then [remainder, root]
        else [root, remainder - root])
      (unpairFinalCost remainder root) := by
  by_cases upperEdge : remainder < root
  · have positive : 0 < root - remainder := by omega
    rw [if_pos upperEdge]
    simpa [Code.unpairFinalCode, unpairFinalCost,
      upperEdge] using
      branchZero_succ positive
        (unpairTest remainder root)
        (id [remainder, root])
  · have zero : root - remainder = 0 := by omega
    rw [if_neg upperEdge]
    simpa [Code.unpairFinalCode, unpairFinalCost,
      upperEdge] using
      branchZero_zero zero
        (unpairTest remainder root)
        (unpairLower remainder root)

def unpairCost (number : Nat) : Nat :=
  let root := Nat.sqrt number
  let remainder := number - root * root
  unpairFinalCost remainder root +
    unpairStateCost number

theorem unpair (number : Nat) :
    EvaluatorCodeFits Code.unpairCode [number]
      [number.unpair.1, number.unpair.2]
      (unpairCost number) := by
  let root := Nat.sqrt number
  let remainder := number - root * root
  have state := unpairState number
  have final := unpairFinal remainder root
  have result := comp final state
  have semantic :
      (if remainder < root then [remainder, root]
        else [root, remainder - root]) =
      [number.unpair.1, number.unpair.2] := by
    have unpairEq :
        number.unpair =
          if remainder < root then (remainder, root)
          else (root, remainder - root) := by
      simp [Nat.unpair, root, remainder]
    rw [unpairEq]
    split <;> rfl
  rw [semantic] at result
  simpa [Code.unpairCode, unpairCost,
    root, remainder] using result

theorem unpairCost_le_linear (number : Nat) :
    unpairCost number ≤
      1000000000 *
        (encodedListSpace [2 * number + 4] + 1) := by
  let root := Nat.sqrt number
  let distance :=
    (root + 1) * (root + 1) - number
  let gap := 2 * root + 1
  let remainder := number - root * root
  let limit := 2 * number + 4
  have rootBound : root ≤ number := by
    simpa [root] using Nat.sqrt_le_self number
  have squareBound : root * root ≤ number := by
    have strict := Nat.sqrt_mul_sqrt_lt_succ number
    have bounded :
        Nat.sqrt number * Nat.sqrt number ≤ number := by
      omega
    simpa [root] using bounded
  have squareIdentity :
      (root + 1) * (root + 1) =
        root * root + (2 * root + 1) := by
    ring
  have distanceBound : distance ≤ limit := by
    simp only [distance, limit]
    omega
  have gapBound : gap ≤ limit := by
    simp only [gap, limit]
    omega
  have remainderBound : remainder ≤ limit := by
    simp only [remainder, limit]
    omega
  have rootLimit : root ≤ limit := by omega
  have numberLimit : number ≤ limit := by omega
  have distanceBits :=
    encodeNat_length_mono distanceBound
  have gapBits := encodeNat_length_mono gapBound
  have remainderBits :=
    encodeNat_length_mono remainderBound
  have rootBits := encodeNat_length_mono rootLimit
  have numberBits := encodeNat_length_mono numberLimit
  have gapSubBits :=
    encodeNat_length_mono
      (show gap - distance ≤ limit by omega)
  have rootSubBits :=
    encodeNat_length_mono
      (show root - remainder ≤ limit by omega)
  have remainderSubBits :=
    encodeNat_length_mono
      (show remainder - root ≤ limit by omega)
  have rootSubPredBits :=
    encodeNat_length_mono
      (show root - remainder - 1 ≤ limit by omega)
  have remainderSuccBits :=
    encodeNat_length_mono
      (show remainder + 1 ≤ limit by omega)
  have rootSuccBits :=
    encodeNat_length_mono
      (show root + 1 ≤ limit by omega)
  have distanceSuccBits :=
    encodeNat_length_mono
      (show distance + 1 ≤ limit by
        simp only [distance, limit]
        omega)
  have gapSuccBits :=
    encodeNat_length_mono
      (show gap + 1 ≤ limit by omega)
  have numberSuccBits :=
    encodeNat_length_mono
      (show number + 1 ≤ limit by omega)
  have sqrtLimitBits :=
    encodeNat_length_mono
      (show 2 * number + 3 ≤ limit by omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  by_cases upperEdge : remainder < root
  · simp [unpairCost, unpairFinalCost,
      unpairStateCost, unpairRemainderStateCost,
      unpairRemainderCost, unpairRemainderArgumentsCost,
      unpairTestCost, unpairTestArgumentsCost,
      sqrtStateCost,
      sqrtInputCost, sqrtLoopCost, subtractCost,
      subtractInputCost, subtractLoopCost,
      branchZeroSuccCost, branchZeroTestCost,
      prependCost, getCost, dropCost, idCost,
      headCost, nilCost, oneCost, zeroCost,
      zeroPrimeCost, tailCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      root, distance, gap, remainder, limit,
      upperEdge, zeroBits, oneBits] at *
    omega
  · simp [unpairCost, unpairFinalCost,
      unpairStateCost, unpairRemainderStateCost,
      unpairRemainderCost, unpairRemainderArgumentsCost,
      unpairTestCost, unpairTestArgumentsCost,
      unpairLowerCost, unpairRightCost,
      unpairRightArgumentsCost, sqrtStateCost,
      sqrtInputCost, sqrtLoopCost, subtractCost,
      subtractInputCost, subtractLoopCost,
      branchZeroZeroCost, branchZeroTestCost,
      prependCost, getCost, dropCost, idCost,
      headCost, nilCost, oneCost, zeroCost,
      zeroPrimeCost, tailCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      root, distance, gap, remainder, limit,
      upperEdge, zeroBits, oneBits] at *
    omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
