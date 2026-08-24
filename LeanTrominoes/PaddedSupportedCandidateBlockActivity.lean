/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Active-value semantics of fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- Removing inactive option slots from one activated block yields precisely
that block's values when active and nothing otherwise. -/
@[simp] theorem filterMap_value_map_activate
    (active : Bool) (block : List (Template Value)) :
    (block.map (Template.activate active)).filterMap Candidate.value =
      if active then block.map Template.value else [] := by
  cases active <;>
    induction block with
    | nil => rfl
    | cons template block induction =>
        simp [Template.activate, induction]

/-- Removing all inactive padded slots recovers the exact compact selected
block stream, including its left-to-right order. -/
theorem filterMap_value_candidates
    (actives : List Bool) (blocks : List (List (Template Value))) :
    (candidates actives blocks).filterMap Candidate.value =
      activeValues actives blocks := by
  induction actives generalizing blocks with
  | nil => rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          rw [candidates, activeValues, List.filterMap_append,
            filterMap_value_map_activate, induction]

/-- Removing inactive padded slots distributes through an outer family of
fixed candidate blocks. -/
theorem filterMap_value_flatMap_candidates
    {Index : Type*} (indices : List Index)
    (actives : Index → List Bool)
    (blocks : Index → List (List (Template Value))) :
    (indices.flatMap fun index =>
        candidates (actives index) (blocks index)).filterMap
          Candidate.value =
      indices.flatMap fun index =>
        activeValues (actives index) (blocks index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      rw [List.flatMap_cons, List.filterMap_append,
        filterMap_value_candidates, induction]
      rfl

end LeanTrominoes.PaddedSupportedCandidateBlocks
