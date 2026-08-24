/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMapRows

/-! # Representative selection under activity-supported candidate maps -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v w

variable {Source : Type u} {First : Type v} {Second : Type w}
  [DecidableEq First] [DecidableEq Second]

/-- Representative selection is invariant under two active-value projections
that induce the same equality relation on all presented active values. -/
theorem selectedRows_mapActiveValue_eq_of_eq_iff_on_filterMap
    (firstProject : Source → First) (secondProject : Source → Second)
    (candidates : List (Candidate Source))
    (sameEquality :
      ∀ first ∈ candidates.filterMap Candidate.value,
        ∀ second ∈ candidates.filterMap Candidate.value,
          firstProject first = firstProject second ↔
            secondProject first = secondProject second) :
    selectedRows
        (candidates.map (Candidate.mapActiveValue firstProject)) =
      selectedRows
        (candidates.map (Candidate.mapActiveValue secondProject)) := by
  unfold selectedRows
  rw [rows_mapActiveValue_eq_of_eq_iff_on_filterMap
    firstProject secondProject candidates sameEquality]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
