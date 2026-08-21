/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterExecution
import LeanTrominoes.UnarySuccessorEqualityFilterFieldsTimeBound
import LeanTrominoes.UnarySuccessorEqualityFilterLengthBounds

/-! # Linear clock bound for unary successor-equality filtering -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

theorem totalTime_le (input : Input) :
    totalTime input ≤ 12 * ((encode input).length + 1) := by
  let rankLength :=
    (UnaryFieldEncoderMachine.unaryFields input.ranks).length
  let sizeLength :=
    (UnaryFieldEncoderMachine.unaryFields input.sizes).length
  let inputLength := (encode input).length
  have inputLengthEq : inputLength = rankLength + (sizeLength + 1) := by
    simp [inputLength, rankLength, sizeLength]
  have outputBound : (outputEncoding input).length ≤ sizeLength := by
    simpa [sizeLength] using outputEncoding_length_le input
  have fieldsBound : fieldsTime input.ranks input.sizes ≤
      4 * (rankLength + sizeLength) := by
    simpa [rankLength, sizeLength] using fieldsTime_le input.valid
  have parseTimeEq :
      parseTime
          (UnaryFieldEncoderMachine.unaryFields input.ranks)
          (UnaryFieldEncoderMachine.unaryFields input.sizes) =
        4 * inputLength := by
    simp [parseTime, rankLength, sizeLength] at inputLengthEq ⊢
    omega
  change totalTime input ≤ 12 * (inputLength + 1)
  unfold totalTime scanTime
  rw [parseTimeEq]
  omega

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
