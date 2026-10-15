/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Proof erasure for filtered attached lists -/

namespace List

/-- Filtering a list while retaining membership proofs and then erasing those
proofs is the same ordered `filterMap` on the original list. -/
theorem filterMap_if_some_eq_map_attach_filter
    {α : Type*} (values : List α) (predicate : α → Prop)
    [DecidablePred predicate] :
    values.filterMap
        (fun value => if predicate value then some value else none) =
      (values.attach.filter fun value => decide (predicate value.1)).map
        Subtype.val := by
  let keep := fun value => decide (predicate value)
  have eraseFilter :
      (values.attach.filter fun value => keep value.1).map Subtype.val =
        values.filter keep := by
    calc
      _ = ((values.filter keep).attach.map
          (Subtype.map id fun _ => List.mem_of_mem_filter)).map
          Subtype.val :=
        congrArg (List.map Subtype.val)
          (List.filter_attach values keep)
      _ = values.filter keep := by
        rw [List.map_map]
        change (values.filter keep).attach.map Subtype.val =
          values.filter keep
        exact List.attach_map_subtype_val (values.filter keep)
  rw [eraseFilter]
  rw [← List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro value _member
  by_cases kept : predicate value <;>
    simp [Option.guard, keep, kept]

/-- Finding in a mapped list is finding with the pulled-back predicate and
then mapping the selected value. -/
theorem find?_map_eq_map_find?
    {α β : Type*} (values : List α) (mapValue : α → β)
    (predicate : β → Bool) :
    (values.map mapValue).find? predicate =
      (values.find? fun value => predicate (mapValue value)).map mapValue := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases selected : predicate (mapValue head) = true
      · simp [List.find?, selected]
      · simp [List.find?, selected, induction]

/-- A first-match search succeeds exactly when the same Boolean predicate is
true somewhere in the list. -/
theorem isSome_find?_eq_any
    {α : Type*} (values : List α) (predicate : α → Bool) :
    (values.find? predicate).isSome = values.any predicate := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases selected : predicate head = true
      · simp [List.find?, selected]
      · simp [List.find?, selected, induction]

end List
