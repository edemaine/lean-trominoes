/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Length of fixed-slot padded candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

theorem candidates_length_of_length_eq
    {Value : Type*} (actives : List Bool)
    (blocks : List (List (Template Value)))
    (lengthEq : actives.length = blocks.length) :
    (candidates actives blocks).length = blocks.flatten.length := by
  induction actives generalizing blocks with
  | nil =>
      have : blocks = [] := List.eq_nil_of_length_eq_zero lengthEq.symm
      subst blocks
      rfl
  | cons active actives induction =>
      cases blocks with
      | nil => simp at lengthEq
      | cons block blocks =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEq
          simp only [candidates, List.length_append, List.length_map,
            List.flatten_cons]
          rw [induction blocks lengthEq]

end LeanTrominoes.PaddedSupportedCandidateBlocks
