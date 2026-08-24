/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateMap

/-! # Optional value streams under candidate maps -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v

variable {Source : Type u} {Target : Type v}

/-- The padded optional-value stream commutes with a candidate value map. -/
@[simp] theorem values_map_mapValue
    (project : Source → Target) (candidates : List (Candidate Source)) :
    values (candidates.map (Candidate.mapValue project)) =
      (values candidates).map (Option.map project) := by
  simp [values, Function.comp_def]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
