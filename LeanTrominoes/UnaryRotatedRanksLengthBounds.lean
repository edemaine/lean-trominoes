/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksInput

/-! # Length bounds for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

@[simp] theorem encode_length (input : Input) :
    (encode input).length =
      (UnaryFieldEncoderMachine.unaryFields input.ranks).length +
        ((UnaryFieldEncoderMachine.unaryFields input.sizes).length + 1) := by
  simp [encode, SeparatedProductEncoding.encode_length]

theorem rotatedRank_le_size (rank size : Nat) (rankLtSize : rank < size) :
    rotatedRank rank size ≤ size := by
  by_cases rankZero : rank = 0
  · simp [rotatedRank, rankZero]
  · simp [rotatedRank, rankZero]
    omega

theorem rotatedRanks_length_bound {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    (UnaryFieldEncoderMachine.unaryFields
      (rotatedRanks ranks sizes)).length ≤
        (UnaryFieldEncoderMachine.unaryFields sizes).length := by
  induction valid with
  | nil => simp [rotatedRanks]
  | @cons rank size ranks sizes rankLtSize valid induction =>
      rw [rotatedRanks,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have headBound := rotatedRank_le_size rank size rankLtSize
      omega

theorem outputEncoding_length_le (input : Input) :
    (outputEncoding input).length ≤
      (UnaryFieldEncoderMachine.unaryFields input.sizes).length := by
  exact rotatedRanks_length_bound input.valid

end UnaryRotatedRanksMachine
end LeanTrominoes
