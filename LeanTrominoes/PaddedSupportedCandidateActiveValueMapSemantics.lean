/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMap

/-! # Optional value streams under activity-supported maps -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v

variable {Source : Type u} {Target : Type v}

/-- The padded optional-value stream commutes with an activity-supported
candidate map. -/
@[simp] theorem values_map_mapActiveValue
    (project : Source → Target) (candidates : List (Candidate Source)) :
    values (candidates.map (Candidate.mapActiveValue project)) =
      (values candidates).map (Option.map project) := by
  simp [values, Function.comp_def]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
