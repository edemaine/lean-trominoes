/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Last-occurrence deduplication with a final sentinel -/

namespace List

variable {Value : Type*} [DecidableEq Value]

/-- Appending a sentinel removes all earlier copies of it, deduplicates every
other value in last-occurrence order, and retains one final sentinel. -/
theorem dedup_append_singleton_eq_filter
    (values : List Value) (sentinel : Value) :
    (values ++ [sentinel]).dedup =
      (values.filter fun value => decide (value ≠ sentinel)).dedup ++
        [sentinel] := by
  induction values with
  | nil => simp
  | cons value values induction =>
      by_cases valueSentinel : value = sentinel
      · subst value
        simp [induction]
      · by_cases valueLater : value ∈ values
        · have valueAppended : value ∈ values ++ [sentinel] :=
            mem_append_left [sentinel] valueLater
          have valueFiltered :
              value ∈ values.filter fun item =>
                decide (item ≠ sentinel) :=
            mem_filter.mpr ⟨valueLater, by simp [valueSentinel]⟩
          rw [cons_append, dedup_cons_of_mem valueAppended,
            filter_cons_of_pos (by simp [valueSentinel]),
            dedup_cons_of_mem valueFiltered, induction]
        · have valueNotAppended : value ∉ values ++ [sentinel] := by
            simp [valueLater, valueSentinel]
          have valueNotFiltered :
              value ∉ values.filter fun item =>
                decide (item ≠ sentinel) := by
            intro valueFiltered
            exact valueLater (mem_of_mem_filter valueFiltered)
          rw [cons_append, dedup_cons_of_notMem valueNotAppended,
            filter_cons_of_pos (by simp [valueSentinel]),
            dedup_cons_of_notMem valueNotFiltered, induction]
          rfl

end List
