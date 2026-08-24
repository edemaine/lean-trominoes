/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Value maps of padded supported candidates -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v

variable {Source : Type u} {Target : Type v}

/-- Map an active optional value while preserving its support bit. -/
def Candidate.mapValue (project : Source → Target)
    (candidate : Candidate Source) : Candidate Target where
  value := candidate.value.map project
  supported := candidate.supported

@[simp] theorem Candidate.mapValue_value
    (project : Source → Target) (candidate : Candidate Source) :
    (candidate.mapValue project).value = candidate.value.map project :=
  rfl

@[simp] theorem Candidate.mapValue_supported
    (project : Source → Target) (candidate : Candidate Source) :
    (candidate.mapValue project).supported = candidate.supported :=
  rfl

/-- Compacting after a padded candidate value map equals mapping after
compacting the original active values. -/
theorem filterMap_value_map_mapValue
    (project : Source → Target) (candidates : List (Candidate Source)) :
    (candidates.map (Candidate.mapValue project)).filterMap
        Candidate.value =
      (candidates.filterMap Candidate.value).map project := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [Candidate.mapValue, induction]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
