/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics

/-! # True counts of last-representative equality rows -/

namespace LeanTrominoes
namespace LastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

theorem countTrue_equalityRow (values : List Value) (value : Value) :
    DelimitedBinaryWordTrueCounts.countTrue (equalityRow values value) =
      values.count value := by
  unfold DelimitedBinaryWordTrueCounts.countTrue
  induction values with
  | nil => rfl
  | cons head values induction =>
      by_cases same : value = head
      · subst head
        rw [show equalityRow (value :: values) value =
          true :: equalityRow values value by simp [equalityRow]]
        simp [induction]
      · have headNe : head ≠ value := Ne.symm same
        rw [show equalityRow (head :: values) value =
          false :: equalityRow values value by simp [equalityRow, same]]
        simp [headNe, induction]

/-- Counting the selected rows gives each deduplicated value's full
occurrence count, in the same last-occurrence order. -/
theorem trueCounts_rows_equalityRows (values : List Value) :
    DelimitedBinaryWordTrueCounts.counts
        (rows ⟨equalityRows values⟩) =
      values.dedup.map fun value => values.count value := by
  rw [rows_equalityRows]
  unfold DelimitedBinaryWordTrueCounts.counts
  rw [List.map_map]
  apply List.map_congr_left
  intro value valueMem
  exact countTrue_equalityRow values value

end LastRepresentativeEqualityRows
end LeanTrominoes
