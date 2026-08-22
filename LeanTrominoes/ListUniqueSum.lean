/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Nodup

/-! # Sums with one potentially nonzero list entry -/

namespace List

/-- A list whose mapped values all vanish has zero mapped sum. -/
theorem sum_map_eq_zero_of_forall
    (values : α → Nat) (items : List α)
    (allZero : ∀ item ∈ items, values item = 0) :
    (items.map values).sum = 0 := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.map_cons, List.sum_cons]
      rw [allZero item (by simp)]
      rw [Nat.zero_add]
      exact induction fun other otherMember =>
        allZero other (by simp [otherMember])

/-- In a duplicate-free list, if every entry other than one selected member
maps to zero, the mapped sum is exactly the selected value. -/
theorem sum_map_eq_of_unique
    [DecidableEq α] (values : α → Nat)
    (items : List α) (selected : α)
    (nodup : items.Nodup) (selectedMember : selected ∈ items)
    (otherZero :
      ∀ item ∈ items, item ≠ selected → values item = 0) :
    (items.map values).sum = values selected := by
  induction items with
  | nil => simp at selectedMember
  | cons item items induction =>
      rw [List.nodup_cons] at nodup
      rcases List.mem_cons.mp selectedMember with selectedHead | selectedTail
      · subst item
        simp only [List.map_cons, List.sum_cons]
        have tailZero : (items.map values).sum = 0 :=
          sum_map_eq_zero_of_forall values items fun other otherMember =>
            otherZero other (by simp [otherMember]) fun otherEq =>
              nodup.1 (otherEq ▸ otherMember)
        rw [tailZero, Nat.add_zero]
      · have headNe : item ≠ selected := by
          intro headEq
          exact nodup.1 (headEq ▸ selectedTail)
        rw [List.map_cons, List.sum_cons,
          otherZero item (by simp) headNe, Nat.zero_add]
        exact induction nodup.2 selectedTail fun other otherMember otherNe =>
          otherZero other (by simp [otherMember]) otherNe

end List
