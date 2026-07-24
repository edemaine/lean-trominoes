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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
