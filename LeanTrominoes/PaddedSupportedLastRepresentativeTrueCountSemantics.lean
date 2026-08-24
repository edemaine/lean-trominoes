/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PaddedSupportedLastRepresentativeSelectionSemantics

/-! # True counts of support-guarded representative rows -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Counting the selected guarded rows gives each supported retained optional
value's full multiplicity in the padded candidate stream. -/
theorem trueCounts_selectedRows
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    DelimitedBinaryWordTrueCounts.counts (selectedRows candidates) =
      ((values candidates).dedup.filter fun value =>
        value ∈ base.map some).map fun value =>
          DelimitedBinaryWordTrueCounts.countTrue
            (LastRepresentativeEqualityRows.equalityRow
              (values candidates) value) := by
  rw [selectedRows_eq base candidates correct]
  unfold DelimitedBinaryWordTrueCounts.counts
  rw [List.map_map]
  apply List.map_congr_left
  intro value valueMember
  have supported : value ∈ base.map some :=
    of_decide_eq_true (List.mem_filter.mp valueMember).2
  simp only [Function.comp_apply]
  unfold SupportedLastRepresentativeEqualityRows.row
  unfold DelimitedBinaryWordTrueCounts.countTrue
  rw [List.count_append]
  simp [supported]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
