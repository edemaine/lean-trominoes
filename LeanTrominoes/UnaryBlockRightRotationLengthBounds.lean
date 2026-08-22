/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationInput

/-! # Length bounds for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

theorem unaryFields_append (first second : List Nat) :
    UnaryFieldEncoderMachine.unaryFields (first ++ second) =
      UnaryFieldEncoderMachine.unaryFields first ++
        UnaryFieldEncoderMachine.unaryFields second := by
  simp [UnaryFieldEncoderMachine.unaryFields]

theorem unaryFields_range'_length_le (start count : Nat) :
    (UnaryFieldEncoderMachine.unaryFields
      (List.range' start count)).length ≤
        count * (start + count) := by
  induction count generalizing start with
  | zero => simp
  | succ count induction =>
      rw [List.range'_succ,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have rest := induction (start + 1)
      nlinarith

theorem rotatedBlock_unaryFields_length_le (blockStart groupSize : Nat) :
    (UnaryFieldEncoderMachine.unaryFields
      (rotatedBlock blockStart groupSize)).length ≤
        groupSize * (blockStart + groupSize) := by
  cases groupSize with
  | zero => simp [rotatedBlock]
  | succ count =>
      rw [rotatedBlock,
        UnaryFieldEncoderMachine.unaryFields_cons]
      rw [← List.range'_eq_map_range]
      simp only [List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have rest := unaryFields_range'_length_le blockStart count
      nlinarith

theorem rotatedBlocks_unaryFields_length_le_square
    {groupSizes blockStarts : List Nat}
    (valid : Valid groupSizes blockStarts) :
    (UnaryFieldEncoderMachine.unaryFields
      (rotatedBlocks groupSizes blockStarts)).length ≤
        ((UnaryFieldEncoderMachine.unaryFields groupSizes).length +
          (UnaryFieldEncoderMachine.unaryFields blockStarts).length) ^ 2 := by
  induction valid with
  | nil => simp [rotatedBlocks]
  | @cons groupSize blockStart groupSizes blockStarts valid induction =>
      rw [rotatedBlocks]
      simp only [unaryFields_append,
        UnaryFieldEncoderMachine.unaryFields_cons,
        List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have head := rotatedBlock_unaryFields_length_le
        blockStart groupSize
      have headSquare :
          (UnaryFieldEncoderMachine.unaryFields
            (rotatedBlock blockStart groupSize)).length ≤
              (groupSize + blockStart + 2) ^ 2 := by
        exact head.trans (by nlinarith)
      calc
        (UnaryFieldEncoderMachine.unaryFields
              (rotatedBlock blockStart groupSize)).length +
            (UnaryFieldEncoderMachine.unaryFields
              (rotatedBlocks groupSizes blockStarts)).length ≤
            (groupSize + blockStart + 2) ^ 2 +
              ((UnaryFieldEncoderMachine.unaryFields groupSizes).length +
                (UnaryFieldEncoderMachine.unaryFields blockStarts).length) ^ 2 :=
          Nat.add_le_add headSquare induction
        _ ≤ ((groupSize + blockStart + 2) +
              ((UnaryFieldEncoderMachine.unaryFields groupSizes).length +
                (UnaryFieldEncoderMachine.unaryFields blockStarts).length)) ^ 2 := by
          rw [add_sq' (groupSize + blockStart + 2)
            ((UnaryFieldEncoderMachine.unaryFields groupSizes).length +
              (UnaryFieldEncoderMachine.unaryFields blockStarts).length)]
          omega
        _ = (groupSize + 1 +
              (UnaryFieldEncoderMachine.unaryFields groupSizes).length +
            (blockStart + 1 +
              (UnaryFieldEncoderMachine.unaryFields blockStarts).length)) ^ 2 := by
          congr 1
          omega

theorem outputEncoding_length_le_square (input : Input) :
    (outputEncoding input).length ≤
      ((UnaryFieldEncoderMachine.unaryFields input.groupSizes).length +
        (UnaryFieldEncoderMachine.unaryFields input.blockStarts).length) ^ 2 := by
  simpa [outputEncoding] using
    rotatedBlocks_unaryFields_length_le_square input.valid

end LeanTrominoes.UnaryBlockRightRotationMachine
