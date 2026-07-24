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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
