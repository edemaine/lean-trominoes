/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Deduplicating before a mapped deduplication -/

namespace List

/-- Removing exact duplicates before mapping does not affect the final
dedup-last result after mapping. -/
theorem dedup_map_dedup (values : List α) (mapping : α → β)
    [DecidableEq α] [DecidableEq β] :
    (values.dedup.map mapping).dedup =
      (values.map mapping).dedup := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases valueLater : value ∈ values
      · rw [List.dedup_cons_of_mem valueLater]
        rw [List.map_cons, List.dedup_cons_of_mem
          (List.mem_map_of_mem valueLater)]
        exact induction
      · rw [List.dedup_cons_of_notMem valueLater, List.map_cons,
          List.map_cons]
        by_cases mappedLater : mapping value ∈ values.map mapping
        · have mappedDedupLater :
              mapping value ∈ values.dedup.map mapping := by
            simpa only [List.mem_map, List.mem_dedup] using mappedLater
          rw [List.dedup_cons_of_mem mappedDedupLater,
            List.dedup_cons_of_mem mappedLater]
          exact induction
        · have mappedDedupNotLater :
              mapping value ∉ values.dedup.map mapping := by
            simpa only [List.mem_map, List.mem_dedup] using mappedLater
          rw [List.dedup_cons_of_notMem mappedDedupNotLater,
            List.dedup_cons_of_notMem mappedLater, induction]

end List
