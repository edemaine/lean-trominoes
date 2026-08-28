/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary-field encoding over a mapped concatenation -/

namespace LeanTrominoes.UnaryFieldEncoderMachine

/-- Encoding a concatenation is the concatenation of the encoded blocks. -/
theorem unaryFields_flatMap {Index : Type}
    (values : List Index) (fields : Index → List Nat) :
    unaryFields (values.flatMap fields) =
      values.flatMap fun value => unaryFields (fields value) := by
  unfold unaryFields
  exact List.flatMap_assoc

end LeanTrominoes.UnaryFieldEncoderMachine

