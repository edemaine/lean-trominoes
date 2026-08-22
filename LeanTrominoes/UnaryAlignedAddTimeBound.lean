/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddExecution
import LeanTrominoes.UnaryAlignedAddLengthBounds

/-! # Linear clock bound for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

theorem fieldTime_le (first second : Nat) :
    fieldTime first second ≤
      2 * ((UnaryFieldEncoderMachine.unaryField first).length +
        (UnaryFieldEncoderMachine.unaryField second).length) := by
  simp [fieldTime]
  omega

theorem fieldsTime_le {firsts seconds : List Nat}
    (valid : Valid firsts seconds) :
    fieldsTime firsts seconds ≤
      2 * ((UnaryFieldEncoderMachine.unaryFields firsts).length +
        (UnaryFieldEncoderMachine.unaryFields seconds).length) := by
  induction valid with
  | nil => simp
  | @cons first second firsts seconds valid induction =>
      rw [fieldsTime_cons,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append]
      have headBound := fieldTime_le first second
      omega

theorem totalTime_le (input : Input) :
    totalTime input ≤ 10 * ((encode input).length + 1) := by
  let firstLength :=
    (UnaryFieldEncoderMachine.unaryFields input.firsts).length
  let secondLength :=
    (UnaryFieldEncoderMachine.unaryFields input.seconds).length
  let inputLength := (encode input).length
  have inputLengthEq :
      inputLength = firstLength + (secondLength + 1) := by
    simp [inputLength, firstLength, secondLength]
  have outputBound :
      (outputEncoding input).length ≤ firstLength + secondLength := by
    simpa [firstLength, secondLength] using outputEncoding_length_le input
  have fieldsBound : fieldsTime input.firsts input.seconds ≤
      2 * (firstLength + secondLength) := by
    simpa [firstLength, secondLength] using fieldsTime_le input.valid
  have parseTimeEq :
      parseTime
          (UnaryFieldEncoderMachine.unaryFields input.firsts)
          (UnaryFieldEncoderMachine.unaryFields input.seconds) =
        4 * inputLength := by
    simp [parseTime, firstLength, secondLength] at inputLengthEq ⊢
    omega
  change totalTime input ≤ 10 * (inputLength + 1)
  unfold totalTime scanTime
  rw [parseTimeEq]
  omega

end UnaryAlignedAddMachine
end LeanTrominoes
