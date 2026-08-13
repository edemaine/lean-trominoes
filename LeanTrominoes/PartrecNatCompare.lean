/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecSubtract

/-!
# Explicit natural comparison programs

The strict comparison `left < right` is detected by whether the truncated
difference `right - left` is positive.  Results are normalized to zero or one.
-/

namespace Turing.ToPartrec.Code

/-- Present `[right, left]` to truncated subtraction. -/
def natLtArgumentsCode : Code :=
  prepend (get 1) (get 0)

@[simp]
theorem natLtArgumentsCode_eval
    (left right : Nat) :
    natLtArgumentsCode.eval [left, right] =
      pure [right, left] := by
  simp [natLtArgumentsCode]

def natLtDifferenceCode : Code :=
  subtractCode.comp natLtArgumentsCode

@[simp]
theorem natLtDifferenceCode_eval
    (left right : Nat) :
    natLtDifferenceCode.eval [left, right] =
      pure [right - left] := by
  simp [natLtDifferenceCode]

/-- Binary code returning one exactly when `left < right`. -/
def natLtCode : Code :=
  normalizeBool natLtDifferenceCode

@[simp]
theorem natLtCode_eval (left right : Nat) :
    natLtCode.eval [left, right] =
      pure [if left < right then 1 else 0] := by
  have normalized :=
    normalizeBool_eval_at natLtDifferenceCode
      [left, right] (right - left)
      (natLtDifferenceCode_eval left right)
  by_cases less : left < right
  · have nonzero : right - left ≠ 0 := by omega
    simpa [natLtCode, less, nonzero] using normalized
  · have zero : right - left = 0 := by omega
    simpa [natLtCode, less, zero] using normalized

/-- Unary code returning one exactly when its input is positive. -/
def natPositiveCode : Code :=
  normalizeBool head

@[simp]
theorem natPositiveCode_eval (number : Nat) :
    natPositiveCode.eval [number] =
      pure [if 0 < number then 1 else 0] := by
  have normalized :=
    normalizeBool_eval_at head [number] number
      (by simp)
  by_cases positive : 0 < number
  · have nonzero : number ≠ 0 := Nat.ne_of_gt positive
    simpa [natPositiveCode, positive, nonzero] using
      normalized
  · have zero : number = 0 := by omega
    simpa [natPositiveCode, positive, zero] using
      normalized

end Turing.ToPartrec.Code
