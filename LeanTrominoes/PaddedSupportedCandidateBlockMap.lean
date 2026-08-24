/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PaddedSupportedCandidateMap

/-! # Value maps of fixed candidate template blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

universe u v

variable {Source : Type u} {Target : Type v}

/-- Map a template value while preserving its eventual support bit. -/
def Template.mapValue (project : Source → Target)
    (template : Template Source) : Template Target where
  value := project template.value
  supported := template.supported

@[simp] theorem Template.mapValue_activate
    (project : Source → Target) (active : Bool)
    (template : Template Source) :
    (template.mapValue project).activate active =
      (template.activate active).mapValue project := by
  cases active <;> rfl

/-- Activation of fixed padded blocks commutes with a value projection. -/
theorem candidates_mapValue
    (project : Source → Target) (actives : List Bool)
    (blocks : List (List (Template Source))) :
    (candidates actives blocks).map
        (PaddedSupportedLastRepresentativeEqualityRows.Candidate.mapValue
          project) =
      candidates actives
        (blocks.map fun block => block.map (Template.mapValue project)) := by
  induction actives generalizing blocks with
  | nil => cases blocks <;> rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          simp only [candidates, List.map_append, List.map_map]
          rw [induction blocks]
          apply congrArg₂ List.append
          · conv_rhs => rw [List.map_map]
            apply List.map_congr_left
            intro template _templateMember
            exact (Template.mapValue_activate
              project active template).symm
          · rfl

end LeanTrominoes.PaddedSupportedCandidateBlocks
