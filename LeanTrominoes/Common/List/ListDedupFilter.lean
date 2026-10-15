/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Commuting last-occurrence deduplication with filtering -/

namespace List

variable {Value : Type*} [DecidableEq Value]

/-- Filtering before or after last-occurrence deduplication gives the same
stable representative order. -/
theorem dedup_filter (predicate : Value → Bool) (values : List Value) :
    (values.filter predicate).dedup = values.dedup.filter predicate := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases selected : predicate value <;>
        by_cases later : value ∈ values <;>
          simp [selected, later, induction]

end List
