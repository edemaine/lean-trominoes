/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecution
import LeanTrominoes.UnaryBlockRightRotationLengthBounds

/-! # Polynomial clock bound for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

theorem remainingOutputsTime_le (blockStart position count : Nat) :
    remainingOutputsTime blockStart position count ≤
      (count + 1) *
        (2 * blockStart + 2 * position + 2 * count + 6) := by
  induction count generalizing position with
  | zero =>
      simp [remainingOutputsTime]
  | succ count induction =>
      rw [remainingOutputsTime]
      have rest := induction (position + 1)
      unfold remainingOutputTime
      nlinarith

theorem positiveBlockTime_le (blockStart count : Nat) :
    positiveBlockTime blockStart count ≤
      10 * (blockStart + count + 3) ^ 2 := by
  have remaining := remainingOutputsTime_le blockStart 0 count
  unfold positiveBlockTime blockCleanupTime firstOutputTime
  nlinarith

theorem zeroBlockTime_le (blockStart : Nat) :
    zeroBlockTime blockStart ≤ 10 * (blockStart + 2) ^ 2 := by
  unfold zeroBlockTime blockCleanupTime
  nlinarith

theorem blockTime_le (blockStart groupSize : Nat) :
    blockTime blockStart groupSize ≤
      10 * (blockStart + groupSize + 2) ^ 2 := by
  cases groupSize with
  | zero =>
      simpa [blockTime] using zeroBlockTime_le blockStart
  | succ count =>
      simpa [blockTime, Nat.add_assoc] using
        positiveBlockTime_le blockStart count

theorem fieldTime_le_square (blockStart groupSize : Nat) :
    blockTime blockStart groupSize +
        ((2 * blockStart + 1) + (2 * groupSize + 1)) ≤
      12 * (blockStart + groupSize + 2) ^ 2 := by
  have block := blockTime_le blockStart groupSize
  nlinarith

theorem fieldsTime_le_square {groupSizes blockStarts : List Nat}
    (valid : Valid groupSizes blockStarts) :
    fieldsTime groupSizes blockStarts ≤
      12 *
        ((UnaryFieldEncoderMachine.unaryFields groupSizes).length +
          (UnaryFieldEncoderMachine.unaryFields blockStarts).length) ^ 2 := by
  induction valid with
  | nil => simp [fieldsTime]
  | @cons groupSize blockStart groupSizes blockStarts valid induction =>
      rw [fieldsTime]
      simp only [UnaryFieldEncoderMachine.unaryFields_cons,
        List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have head := fieldTime_le_square blockStart groupSize
      let tailLength :=
        (UnaryFieldEncoderMachine.unaryFields groupSizes).length +
          (UnaryFieldEncoderMachine.unaryFields blockStarts).length
      let headLength := blockStart + groupSize + 2
      have squares : tailLength ^ 2 + headLength ^ 2 ≤
          (tailLength + headLength) ^ 2 := by
        rw [add_sq' tailLength headLength]
        omega
      calc
        fieldsTime groupSizes blockStarts +
              (blockTime blockStart groupSize +
                ((2 * blockStart + 1) + (2 * groupSize + 1))) ≤
            12 * tailLength ^ 2 + 12 * headLength ^ 2 :=
          Nat.add_le_add induction head
        _ = 12 * (tailLength ^ 2 + headLength ^ 2) := by ring
        _ ≤ 12 * (tailLength + headLength) ^ 2 :=
          Nat.mul_le_mul_left 12 squares
        _ = 12 *
            (groupSize + 1 +
                (UnaryFieldEncoderMachine.unaryFields groupSizes).length +
              (blockStart + 1 +
                (UnaryFieldEncoderMachine.unaryFields blockStarts).length)) ^ 2 := by
          congr 2
          simp only [tailLength, headLength]
          omega

theorem totalTime_le (input : Input) :
    totalTime input ≤ 20 * ((encode input).length + 1) ^ 2 := by
  let sizeLength :=
    (UnaryFieldEncoderMachine.unaryFields input.groupSizes).length
  let startLength :=
    (UnaryFieldEncoderMachine.unaryFields input.blockStarts).length
  let inputLength := (encode input).length
  have inputLengthEq : inputLength = sizeLength + (startLength + 1) := by
    simp [inputLength, sizeLength, startLength, encode,
      SeparatedProductEncoding.encode]
  have outputBound : (outputEncoding input).length ≤
      (sizeLength + startLength) ^ 2 := by
    simpa [sizeLength, startLength] using
      outputEncoding_length_le_square input
  have fieldsBound : fieldsTime input.groupSizes input.blockStarts ≤
      12 * (sizeLength + startLength) ^ 2 := by
    simpa [sizeLength, startLength] using
      fieldsTime_le_square input.valid
  have parseTimeEq :
      parseTime
          (UnaryFieldEncoderMachine.unaryFields input.groupSizes)
          (UnaryFieldEncoderMachine.unaryFields input.blockStarts) =
        4 * inputLength := by
    simp [parseTime, sizeLength, startLength] at inputLengthEq ⊢
    omega
  change totalTime input ≤ 20 * (inputLength + 1) ^ 2
  unfold totalTime scanTime
  rw [parseTimeEq, inputLengthEq]
  nlinarith

end LeanTrominoes.UnaryBlockRightRotationMachine
