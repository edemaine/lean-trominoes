/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Last-occurrence deduplication across an append -/

namespace LeanTrominoes

/-- Before appending a suffix, entries already represented in that suffix may
be filtered out without changing last-occurrence deduplication. -/
theorem List.dedup_append_eq_dedup_filter_append
    {Value : Type*} [DecidableEq Value]
    (initial suffix : List Value) :
    (initial ++ suffix).dedup =
      ((initial.filter fun value => decide (value ∉ suffix)) ++ suffix).dedup := by
  induction initial with
  | nil => rfl
  | cons value initial induction =>
      by_cases valueInSuffix : value ∈ suffix
      · have valueInTail : value ∈ initial ++ suffix :=
          List.mem_append_right initial valueInSuffix
        simp [valueInSuffix, valueInTail, induction]
      · have membership :
          value ∈ initial ++ suffix ↔
            value ∈
              (initial.filter fun item => decide (item ∉ suffix)) ++ suffix := by
          simp [valueInSuffix]
        simp only [List.cons_append, List.filter_cons, decide_eq_true_eq]
        rw [if_pos valueInSuffix]
        change (value :: (initial ++ suffix)).dedup =
          (value ::
            ((initial.filter fun item => decide (item ∉ suffix)) ++
              suffix)).dedup
        by_cases valueInInitial : value ∈ initial ++ suffix
        · rw [List.dedup_cons_of_mem valueInInitial,
            List.dedup_cons_of_mem (membership.mp valueInInitial), induction]
        · rw [List.dedup_cons_of_notMem valueInInitial,
            List.dedup_cons_of_notMem
              (fun member => valueInInitial (membership.mpr member)), induction]

/-- Deduplicating an append retains the deduplicated prefix entries absent
from the suffix, followed by the suffix's own last-occurrence order. -/
theorem List.dedup_append_eq_filtered_prefix_append
    {Value : Type*} [DecidableEq Value]
    (initial suffix : List Value) :
    (initial ++ suffix).dedup =
      (initial.filter fun value => decide (value ∉ suffix)).dedup ++
        suffix.dedup := by
  rw [List.dedup_append_eq_dedup_filter_append]
  apply List.Disjoint.dedup_append
  rw [List.disjoint_left]
  intro value valueInPrefix valueInSuffix
  have absent : value ∉ suffix := by
    simpa using (List.mem_filter.mp valueInPrefix).2
  exact absent valueInSuffix

end LeanTrominoes
