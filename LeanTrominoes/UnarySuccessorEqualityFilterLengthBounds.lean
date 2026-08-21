/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterInput

/-! # Length bounds for unary successor-equality filtering -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

@[simp] theorem encode_length (input : Input) :
    (encode input).length =
      (UnaryFieldEncoderMachine.unaryFields input.ranks).length +
        ((UnaryFieldEncoderMachine.unaryFields input.sizes).length + 1) := by
  simp [encode, SeparatedProductEncoding.encode_length]

theorem selectedValue_le_size (rank size : Nat) :
    selectedValue rank size ≤ size := by
  by_cases selected : size = rank + 1
  · simp [selectedValue, selected]
  · simp [selectedValue, selected]

theorem selectedValues_length_bound {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    (UnaryFieldEncoderMachine.unaryFields
      (selectedValues ranks sizes)).length ≤
        (UnaryFieldEncoderMachine.unaryFields sizes).length := by
  induction valid with
  | nil => simp [selectedValues]
  | @cons rank size ranks sizes rankLtSize valid induction =>
      rw [selectedValues]
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append,
        UnaryFieldEncoderMachine.unaryField_length]
      have headBound := selectedValue_le_size rank size
      omega

theorem outputEncoding_length_le (input : Input) :
    (outputEncoding input).length ≤
      (UnaryFieldEncoderMachine.unaryFields input.sizes).length := by
  exact selectedValues_length_bound input.valid

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
