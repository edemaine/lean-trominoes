/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupRowsExecution
import LeanTrominoes.LastTrueUnaryValueLookupLocalTimeBounds

/-! # Row-loop time bounds for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

theorem rowsTime_le {rows : List (List Bool)} {values : List Nat}
    (valid : RowsValid values rows) :
    rowsTime rows values ≤
      8 * rows.length *
        ((UnaryFieldEncoderMachine.unaryFields values).length + 1) := by
  induction valid with
  | nil => simp [rowsTime]
  | @cons row rows rowValid rest induction =>
      have head := rowTime_le rowValid
      rw [rowsTime]
      calc
        rowsTime rows values + rowTime row values ≤
            8 * rows.length *
                ((UnaryFieldEncoderMachine.unaryFields values).length + 1) +
              8 *
                ((UnaryFieldEncoderMachine.unaryFields values).length + 1) :=
          Nat.add_le_add induction head
        _ = 8 * (rows.length + 1) *
            ((UnaryFieldEncoderMachine.unaryFields values).length + 1) := by
          ring

theorem rowsTime_le_input_square (input : Input) :
    rowsTime input.rows input.values ≤
      8 * (encode input).length ^ 2 := by
  let inputLength := (encode input).length
  let valueLength :=
    (UnaryFieldEncoderMachine.unaryFields input.values).length
  have rawBound := rowsTime_le input.valid
  have rowCountBound : input.rows.length ≤ inputLength := by
    have rowsBound := rows_length_le_encode_length input.rows
    simp [inputLength] at rowsBound ⊢
    exact rowsBound.trans (Nat.le_add_right _ _)
  have valueLengthBound : valueLength + 1 ≤ inputLength := by
    simp [inputLength, valueLength]
  have productBound :
      input.rows.length * (valueLength + 1) ≤
        inputLength * inputLength :=
    Nat.mul_le_mul rowCountBound valueLengthBound
  calc
    rowsTime input.rows input.values ≤
        8 * input.rows.length * (valueLength + 1) := by
      simpa [valueLength] using rawBound
    _ = 8 * (input.rows.length * (valueLength + 1)) := by ring
    _ ≤ 8 * (inputLength * inputLength) :=
      Nat.mul_le_mul_left 8 productBound
    _ = 8 * (encode input).length ^ 2 := by
      simp [inputLength, pow_two]

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
