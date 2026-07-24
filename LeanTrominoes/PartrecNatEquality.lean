import LeanTrominoes.PartrecSubtract

/-!
# Explicit natural equality

Equality is the conjunction of the two truncated differences being zero.
This fixed binary predicate is used both by the strip base case and by
first-occurrence searches through encoded motif cells.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Swap a pair of native natural fields. -/
def swapPairCode : Code :=
  prepend (get 1) (get 0)

@[simp]
theorem swapPairCode_eval (left right : Nat) :
    swapPairCode.eval [left, right] =
      pure [right, left] := by
  simp [swapPairCode]

/-- Truncated reverse difference `right - left`. -/
def reverseSubtractCode : Code :=
  subtractCode.comp swapPairCode

@[simp]
theorem reverseSubtractCode_eval (left right : Nat) :
    reverseSubtractCode.eval [left, right] =
      pure [right - left] := by
  simp [reverseSubtractCode]

/-- Binary code returning one exactly when its inputs are equal. -/
def natEqCode : Code :=
  boolAnd (isZero subtractCode)
    (isZero reverseSubtractCode)

@[simp]
theorem natEqCode_eval (left right : Nat) :
    natEqCode.eval [left, right] =
      pure [if left = right then 1 else 0] := by
  let values := [left, right]
  let forwardTag :=
    if left - right = 0 then 1 else 0
  let reverseTag :=
    if right - left = 0 then 1 else 0
  have forwardEval :=
    isZero_eval_at subtractCode values
      (left - right) (subtractCode_eval left right)
  have reverseEval :=
    isZero_eval_at reverseSubtractCode values
      (right - left) (reverseSubtractCode_eval left right)
  have combined :=
    boolAnd_eval_at (isZero subtractCode)
      (isZero reverseSubtractCode) values
      forwardTag reverseTag forwardEval reverseEval
  by_cases equal : left = right
  · subst right
    simpa [natEqCode, values, forwardTag,
      reverseTag] using combined
  · rcases lt_or_gt_of_ne equal with less | greater
    · have forward : left - right = 0 := by omega
      have reverse : right - left ≠ 0 := by omega
      simpa [natEqCode, values, forwardTag,
        reverseTag, forward, reverse, equal] using combined
    · have forward : left - right ≠ 0 := by omega
      simpa [natEqCode, values, forwardTag,
        reverseTag, forward, equal] using combined

end Turing.ToPartrec.Code
