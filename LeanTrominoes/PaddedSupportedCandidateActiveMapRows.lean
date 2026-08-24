/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMapValueEquality

/-! # Guarded rows under activity-supported candidate maps -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v w

variable {Source : Type u} {First : Type v} {Second : Type w}
  [DecidableEq First] [DecidableEq Second]

/-- Projections with the same equality relation on active values produce
identical guarded equality-row inputs. -/
theorem rows_mapActiveValue_eq_of_eq_iff_on_filterMap
    (firstProject : Source → First) (secondProject : Source → Second)
    (candidates : List (Candidate Source))
    (sameEquality :
      ∀ first ∈ candidates.filterMap Candidate.value,
        ∀ second ∈ candidates.filterMap Candidate.value,
          firstProject first = firstProject second ↔
            secondProject first = secondProject second) :
    rows (candidates.map (Candidate.mapActiveValue firstProject)) =
      rows (candidates.map (Candidate.mapActiveValue secondProject)) := by
  unfold rows
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro candidate candidateMember
  simp only [Function.comp_apply]
  unfold row values
    LastRepresentativeEqualityRows.equalityRow
  simp only [Candidate.mapActiveValue_value,
    Candidate.mapActiveValue_supported, List.map_map]
  apply congrArg₂ (fun equalityBits rejection =>
    equalityBits ++ [rejection])
  · apply List.map_congr_left
    intro other otherMember
    exact Bool.decide_congr
      (option_map_eq_iff_of_eq_iff_on_filterMap
        firstProject secondProject candidates sameEquality
        candidate other candidateMember otherMember)
  · rfl

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
