/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Finite list sums partitioned into fibers -/

namespace List

/-- A noduplicated list of keys that covers every value partitions a
natural-valued list sum into the corresponding filtered fibers. -/
theorem sum_map_eq_sum_fibers
    {Value Key : Type*} [DecidableEq Key]
    (group : Value -> Key) (weight : Value -> Nat)
    (values : List Value) (keys : List Key)
    (keysNodup : keys.Nodup)
    (covered : ∀ value ∈ values, group value ∈ keys) :
    (values.map weight).sum =
      (keys.map fun key =>
        ((values.filter fun value => group value = key).map weight).sum).sum := by
  induction keys generalizing values with
  | nil =>
      have valuesEmpty : values = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value valueMember
        simpa using covered value valueMember
      subst values
      rfl
  | cons key keys induction =>
      have keyNotMember : key ∉ keys :=
        (List.nodup_cons.mp keysNodup).1
      have keysNodup' : keys.Nodup :=
        (List.nodup_cons.mp keysNodup).2
      let remaining :=
        values.filter fun value => group value ≠ key
      have remainingCovered :
          ∀ value ∈ remaining, group value ∈ keys := by
        intro value valueMember
        have memberAndNe := List.mem_filter.mp valueMember
        have inKeys := covered value memberAndNe.1
        simp only [List.mem_cons] at inKeys
        have valueNe : group value ≠ key := by
          simpa only [decide_eq_true_eq] using memberAndNe.2
        exact inKeys.resolve_left valueNe
      have tailPartition :=
        induction remaining keysNodup' remainingCovered
      have tailFibers :
          (keys.map fun later =>
            ((remaining.filter fun value => group value = later).map
              weight).sum) =
            keys.map fun later =>
              ((values.filter fun value => group value = later).map
                weight).sum := by
        apply List.map_congr_left
        intro later laterMember
        have laterNe : later ≠ key := by
          intro equal
          exact keyNotMember (equal ▸ laterMember)
        have filterEq :
            (values.filter fun value => group value ≠ key).filter
                (fun value => group value = later) =
              values.filter fun value => group value = later := by
          rw [List.filter_filter]
          apply congrArg
            (fun predicate : Value -> Bool => values.filter predicate)
          funext value
          by_cases equalLater : group value = later
          · simp [equalLater, laterNe]
          · simp [equalLater]
        simpa only [remaining] using congrArg
          (fun selected => (selected.map weight).sum) filterEq
      have split :=
        sum_map_filter_add_sum_map_filter_not
          (fun value => group value = key) weight values
      simp only [List.map_cons, List.sum_cons]
      rw [← split, show
        values.filter (fun value => ¬(group value = key)) = remaining by
          rfl]
      rw [tailPartition, tailFibers]

/-- In a duplicate-free list, looking up every element in the whole list
enumerates exactly the consecutive list indices. -/
theorem map_idxOf_self_eq_range
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (nodup : values.Nodup) :
    values.map (fun value => values.idxOf value) =
      List.range values.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headNotMember : head ∉ tail :=
        (List.nodup_cons.mp nodup).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp nodup).2
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons]
      congr 1
      · simp
      rw [← induction tailNodup]
      rw [List.map_map]
      apply List.map_congr_left
      intro value valueMember
      have headNe : head ≠ value := by
        intro equal
        exact headNotMember (equal ▸ valueMember)
      simp [headNe]

end List
