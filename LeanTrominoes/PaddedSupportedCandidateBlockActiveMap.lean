/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMap
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Activity-supported maps of fixed candidate blocks -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

universe u v

variable {Source : Type u} {Target : Type v}

/-- Map a template value and replace its support tag by unconditional
support whenever the containing block is active. -/
def Template.mapActiveValue (project : Source → Target)
    (template : Template Source) : Template Target where
  value := project template.value
  supported := true

@[simp] theorem Template.mapActiveValue_activate
    (project : Source → Target) (active : Bool)
    (template : Template Source) :
    (template.mapActiveValue project).activate active =
      (template.activate active).mapActiveValue project := by
  cases active <;> rfl

/-- Activation of fixed padded blocks commutes with an activity-supported
value projection. -/
theorem candidates_mapActiveValue
    (project : Source → Target) (actives : List Bool)
    (blocks : List (List (Template Source))) :
    (candidates actives blocks).map
        (PaddedSupportedLastRepresentativeEqualityRows.Candidate.mapActiveValue
          project) =
      candidates actives
        (blocks.map fun block =>
          block.map (Template.mapActiveValue project)) := by
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
            exact (Template.mapActiveValue_activate
              project active template).symm
          · rfl

end LeanTrominoes.PaddedSupportedCandidateBlocks
