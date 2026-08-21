/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterInput

/-! # Field-loop time bounds for unary successor-equality filtering -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

theorem fieldTime_le (rank size : Nat) (rankLtSize : rank < size) :
    fieldTime rank size ≤
      4 * ((UnaryFieldEncoderMachine.unaryField rank).length +
        (UnaryFieldEncoderMachine.unaryField size).length) := by
  by_cases selected : size = rank + 1
  · simp [fieldTime, selected]
    omega
  · simp [fieldTime, selected]
    omega

theorem fieldsTime_le {ranks sizes : List Nat}
    (valid : Valid ranks sizes) :
    fieldsTime ranks sizes ≤
      4 * ((UnaryFieldEncoderMachine.unaryFields ranks).length +
        (UnaryFieldEncoderMachine.unaryFields sizes).length) := by
  induction valid with
  | nil => simp
  | @cons rank size ranks sizes rankLtSize valid induction =>
      rw [fieldsTime_cons,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      simp only [List.length_append]
      have headBound := fieldTime_le rank size rankLtSize
      omega

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
