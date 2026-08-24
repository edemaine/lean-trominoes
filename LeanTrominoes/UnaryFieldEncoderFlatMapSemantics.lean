/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary-field encoding over concatenated lists -/

namespace LeanTrominoes.UnaryFieldEncoderMachine

@[simp] theorem unaryFields_append (first second : List Nat) :
    unaryFields (first ++ second) =
      unaryFields first ++ unaryFields second := by
  induction first with
  | nil => rfl
  | cons number first induction =>
      simp only [List.cons_append, unaryFields_cons,
        List.append_assoc, induction]

@[simp] theorem unaryFields_flatten (blocks : List (List Nat)) :
    unaryFields blocks.flatten = blocks.flatMap unaryFields := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.flatten_cons, unaryFields_append,
        List.flatMap_cons, induction]

end LeanTrominoes.UnaryFieldEncoderMachine
