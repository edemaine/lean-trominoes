/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Fixed candidate blocks mapped over one index list -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

variable {Index Value : Type*}

/-- Compact selection of equally mapped activation bits and template blocks
is the flat map over exactly the Boolean-filtered indices. -/
theorem activeValues_map_eq_filter_flatMap
    (indices : List Index) (active : Index → Bool)
    (block : Index → List (Template Value)) :
    activeValues (indices.map active) (indices.map block) =
      (indices.filter active).flatMap fun index =>
        (block index).map Template.value := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      cases accepted : active index <;>
        simp [activeValues, accepted, induction]

end LeanTrominoes.PaddedSupportedCandidateBlocks
