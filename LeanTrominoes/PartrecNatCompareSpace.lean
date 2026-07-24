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
