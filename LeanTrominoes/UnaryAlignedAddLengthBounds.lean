/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddInput

/-! # Length bounds for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

@[simp] theorem encode_length (input : Input) :
    (encode input).length =
      (UnaryFieldEncoderMachine.unaryFields input.firsts).length +
        ((UnaryFieldEncoderMachine.unaryFields input.seconds).length + 1) := by
  simp [encode, SeparatedProductEncoding.encode_length]

theorem sums_length_bound {firsts seconds : List Nat}
    (valid : Valid firsts seconds) :
    (UnaryFieldEncoderMachine.unaryFields
      (sums firsts seconds)).length ≤
        (UnaryFieldEncoderMachine.unaryFields firsts).length +
          (UnaryFieldEncoderMachine.unaryFields seconds).length := by
  induction valid with
  | nil => simp [sums]
  | @cons first second firsts seconds valid induction =>
      rw [sums,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      omega

theorem outputEncoding_length_le (input : Input) :
    (outputEncoding input).length ≤
      (UnaryFieldEncoderMachine.unaryFields input.firsts).length +
        (UnaryFieldEncoderMachine.unaryFields input.seconds).length := by
  exact sums_length_bound input.valid

end UnaryAlignedAddMachine
end LeanTrominoes
