/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationListExecution

/-! # Semantics of accumulated unary block-rotation output -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

theorem reversedUnaryField_eq (value : Nat) :
    reversedUnaryField value =
      (UnaryFieldEncoderMachine.unaryField value).reverse := by
  simp [reversedUnaryField, UnaryFieldEncoderMachine.unaryField]

theorem remainingOutputReverse_eq (blockStart position count : Nat) :
    remainingOutputReverse blockStart position count =
      (UnaryFieldEncoderMachine.unaryFields
        (List.range' (blockStart + position) count)).reverse := by
  induction count generalizing position with
  | zero =>
      simp [remainingOutputReverse,
        UnaryFieldEncoderMachine.unaryFields]
  | succ count induction =>
      rw [remainingOutputReverse, induction, reversedUnaryField_eq,
        List.range'_succ,
        UnaryFieldEncoderMachine.unaryFields_cons,
        List.reverse_append]
      congr 2

theorem positiveBlockOutputReverse_eq (blockStart count : Nat) :
    positiveBlockOutputReverse blockStart count =
      (UnaryFieldEncoderMachine.unaryFields
        (rotatedBlock blockStart (count + 1))).reverse := by
  rw [positiveBlockOutputReverse,
    remainingOutputReverse_eq, reversedUnaryField_eq]
  simp only [rotatedBlock,
    UnaryFieldEncoderMachine.unaryFields_cons,
    List.reverse_append]
  rw [List.range'_eq_map_range]
  simp only [Nat.add_zero]

theorem blockOutputReverse_eq (blockStart groupSize : Nat) :
    blockOutputReverse blockStart groupSize =
      (UnaryFieldEncoderMachine.unaryFields
        (rotatedBlock blockStart groupSize)).reverse := by
  cases groupSize with
  | zero =>
      simp [blockOutputReverse, rotatedBlock,
        UnaryFieldEncoderMachine.unaryFields]
  | succ count =>
      simpa [blockOutputReverse] using
        positiveBlockOutputReverse_eq blockStart count

theorem blocksOutputReverse_eq {groupSizes blockStarts : List Nat}
    (valid : Valid groupSizes blockStarts) :
    blocksOutputReverse groupSizes blockStarts =
      (UnaryFieldEncoderMachine.unaryFields
        (rotatedBlocks groupSizes blockStarts)).reverse := by
  induction valid with
  | nil =>
      simp [blocksOutputReverse, rotatedBlocks,
        UnaryFieldEncoderMachine.unaryFields]
  | @cons groupSize blockStart groupSizes blockStarts valid induction =>
      rw [blocksOutputReverse, rotatedBlocks, induction,
        blockOutputReverse_eq]
      simp [UnaryFieldEncoderMachine.unaryFields,
        List.reverse_append]

end LeanTrominoes.UnaryBlockRightRotationMachine
