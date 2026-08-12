import LeanTrominoes.PartrecMultiply
import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecNatCompare

/-!
# Explicit forward pairing

`PartrecUnpair` decodes the standard `Nat.pair` representation.  This file
supplies the converse program.  It computes the square of the larger input,
adds the appropriate lower-order fields, and selects the defining branch of
`Nat.pair` with the explicit strict-comparison program.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Duplicate the first input for squaring. -/
def natPairLeftSquareArgumentsCode : Code :=
  prepend (get 0) (get 0)

/-- Duplicate the second input for squaring. -/
def natPairRightSquareArgumentsCode : Code :=
  prepend (get 1) (get 1)

@[simp]
theorem natPairLeftSquareArgumentsCode_eval (left right : Nat) :
    natPairLeftSquareArgumentsCode.eval [left, right] =
      pure [left, left] := by
  simp [natPairLeftSquareArgumentsCode]

@[simp]
theorem natPairRightSquareArgumentsCode_eval (left right : Nat) :
    natPairRightSquareArgumentsCode.eval [left, right] =
      pure [right, right] := by
  simp [natPairRightSquareArgumentsCode]

/-- Square the first input. -/
def natPairLeftSquareCode : Code :=
  natMultiplyCode.comp natPairLeftSquareArgumentsCode

/-- Square the second input. -/
def natPairRightSquareCode : Code :=
  natMultiplyCode.comp natPairRightSquareArgumentsCode

@[simp]
theorem natPairLeftSquareCode_eval (left right : Nat) :
    natPairLeftSquareCode.eval [left, right] =
      pure [left * left] := by
  simp [natPairLeftSquareCode]

@[simp]
theorem natPairRightSquareCode_eval (left right : Nat) :
    natPairRightSquareCode.eval [left, right] =
      pure [right * right] := by
  simp [natPairRightSquareCode]

/-- Arguments `[right², left]` for the `left < right` branch. -/
def natPairLowerArgumentsCode : Code :=
  prepend natPairRightSquareCode (get 0)

/-- The value `right² + left` used when `left < right`. -/
def natPairLowerCode : Code :=
  natAddCode.comp natPairLowerArgumentsCode

@[simp]
theorem natPairLowerCode_eval (left right : Nat) :
    natPairLowerCode.eval [left, right] =
      pure [right * right + left] := by
  simp [natPairLowerCode, natPairLowerArgumentsCode]

/-- Arguments `[left², left]` for the first sum in the other branch. -/
def natPairUpperFirstArgumentsCode : Code :=
  prepend natPairLeftSquareCode (get 0)

/-- Compute `left² + left`. -/
def natPairUpperFirstCode : Code :=
  natAddCode.comp natPairUpperFirstArgumentsCode

@[simp]
theorem natPairUpperFirstCode_eval (left right : Nat) :
    natPairUpperFirstCode.eval [left, right] =
      pure [left * left + left] := by
  simp [natPairUpperFirstCode,
    natPairUpperFirstArgumentsCode]

/-- Arguments `[left² + left, right]` for the final upper-branch sum. -/
def natPairUpperArgumentsCode : Code :=
  prepend natPairUpperFirstCode (get 1)

/-- The value `left² + left + right` used when `right ≤ left`. -/
def natPairUpperCode : Code :=
  natAddCode.comp natPairUpperArgumentsCode

@[simp]
theorem natPairUpperCode_eval (left right : Nat) :
    natPairUpperCode.eval [left, right] =
      pure [left * left + left + right] := by
  simp [natPairUpperCode, natPairUpperArgumentsCode]

/-- Binary code computing Mathlib's standard natural pairing function. -/
def natPairCode : Code :=
  branchZero natLtCode natPairUpperCode natPairLowerCode

@[simp]
theorem natPairCode_eval (left right : Nat) :
    natPairCode.eval [left, right] =
      pure [Nat.pair left right] := by
  by_cases less : left < right
  · have evaluated := branchZero_eval_succ_at
      natLtCode natPairUpperCode natPairLowerCode
      [left, right] 1
      (by simp [less])
      [right * right + left]
      (natPairLowerCode_eval left right)
      (by omega)
    simpa [natPairCode, Nat.pair, less] using evaluated
  · have evaluated := branchZero_eval_zero_at
      natLtCode natPairUpperCode natPairLowerCode
      [left, right] 0
      (by simp [less])
      [left * left + left + right]
      (natPairUpperCode_eval left right)
      rfl
    simpa [natPairCode, Nat.pair, less] using evaluated

end Turing.ToPartrec.Code
