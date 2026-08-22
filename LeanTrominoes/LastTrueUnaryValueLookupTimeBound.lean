/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupExecution
import LeanTrominoes.LastTrueUnaryValueLookupRowsTimeBound

/-! # Quadratic clock bound for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

theorem totalTime_le (input : Input) :
    totalTime input ≤
      20 * ((encode input).length ^ 2 + (encode input).length + 1) := by
  let rowLength := (DelimitedBinaryWords.encode ⟨input.rows⟩).length
  let valueLength :=
    (UnaryFieldEncoderMachine.unaryFields input.values).length
  let inputLength := (encode input).length
  have inputLengthEq : inputLength = rowLength + (valueLength + 1) := by
    simp [inputLength, rowLength, valueLength]
  have outputBound :
      (outputEncoding input).length ≤ inputLength ^ 2 := by
    simpa [inputLength] using outputEncoding_length_le_square input
  have rowsBound : rowsTime input.rows input.values ≤
      8 * inputLength ^ 2 := by
    simpa [inputLength] using rowsTime_le_input_square input
  have valueBound : valueLength ≤ inputLength := by
    omega
  have parseTimeEq :
      parseTime
          (DelimitedBinaryWords.encode ⟨input.rows⟩)
          (UnaryFieldEncoderMachine.unaryFields input.values) =
        4 * inputLength := by
    simp [parseTime, rowLength, valueLength] at inputLengthEq ⊢
    omega
  change totalTime input ≤
    20 * (inputLength ^ 2 + inputLength + 1)
  unfold totalTime scanTime
  rw [parseTimeEq]
  omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
