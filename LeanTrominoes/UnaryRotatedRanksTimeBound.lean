/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksExecution
import LeanTrominoes.UnaryRotatedRanksLengthBounds

/-! # Linear clock bound for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

theorem fieldTime_le (rank size : Nat) :
    fieldTime rank size ≤
      3 * ((UnaryFieldEncoderMachine.unaryField rank).length +
        (UnaryFieldEncoderMachine.unaryField size).length) := by
  by_cases rankZero : rank = 0
  · subst rank
    simp [fieldTime]
    omega
  · simp [fieldTime, rankZero]
    omega

theorem fieldsTime_le {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    fieldsTime ranks sizes ≤
      3 * ((UnaryFieldEncoderMachine.unaryFields ranks).length +
        (UnaryFieldEncoderMachine.unaryFields sizes).length) := by
  induction valid with
  | nil => simp
  | @cons rank size ranks sizes rankLtSize valid induction =>
      rw [fieldsTime_cons,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append]
      have headBound := fieldTime_le rank size
      omega

theorem totalTime_le (input : Input) :
    totalTime input ≤ 10 * ((encode input).length + 1) := by
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
      3 * (rankLength + sizeLength) := by
    simpa [rankLength, sizeLength] using fieldsTime_le input.valid
  have parseTimeEq :
      parseTime
          (UnaryFieldEncoderMachine.unaryFields input.ranks)
          (UnaryFieldEncoderMachine.unaryFields input.sizes) =
        4 * inputLength := by
    simp [parseTime, rankLength, sizeLength] at inputLengthEq ⊢
    omega
  change totalTime input ≤ 10 * (inputLength + 1)
  unfold totalTime scanTime
  rw [parseTimeEq]
  omega

end UnaryRotatedRanksMachine
end LeanTrominoes
