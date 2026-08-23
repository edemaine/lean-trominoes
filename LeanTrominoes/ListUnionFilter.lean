/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Filtering canonical list unions -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- List union using the `BEq` canonically induced by a chosen
`DecidableEq`, matching Mathlib's last-occurrence deduplication lemmas. -/
def decidableListUnion {Value : Type*} [DecidableEq Value]
    (first second : List Value) : List Value :=
  @List.union Value instBEqOfDecidableEq first second

/-- Canonical list union retains the deduplicated entries of its first
argument that are absent from its second argument, followed by the second
argument unchanged. -/
theorem decidableListUnion_eq_filteredDedup_append
    {Value : Type*} [DecidableEq Value]
    (first second : List Value) :
    decidableListUnion first second =
      (first.filter fun value => decide (value ∉ second)).dedup ++
        second := by
  have unionFilter :
      decidableListUnion first second =
        decidableListUnion
          (first.filter fun value => decide (value ∉ second)) second := by
    induction first with
    | nil => rfl
    | cons value rest induction =>
        unfold decidableListUnion at induction ⊢
        by_cases valueMember : value ∈ second
        · rw [List.filter_cons_of_neg (by simp [valueMember])]
          have valueUnion :
              value ∈
                @List.union Value instBEqOfDecidableEq rest second := by
            exact List.mem_union_right rest valueMember
          change List.insert value
              (@List.union Value instBEqOfDecidableEq rest second) =
            @List.union Value instBEqOfDecidableEq
              (rest.filter fun value => decide (value ∉ second)) second
          rw [List.insert_of_mem valueUnion]
          exact induction
        · rw [List.filter_cons_of_pos (by simp [valueMember])]
          change List.insert value
              (@List.union Value instBEqOfDecidableEq rest second) =
            List.insert value
              (@List.union Value instBEqOfDecidableEq
                (rest.filter fun value => decide (value ∉ second)) second)
          exact congrArg (List.insert value) induction
  have filteredDisjoint :
      List.Disjoint
        (first.filter fun value => decide (value ∉ second)) second := by
    rw [List.disjoint_left]
    intro value valueFiltered valueSecond
    have valueAbsent : value ∉ second := by
      simpa only [decide_eq_true_eq] using
        (List.mem_filter.mp valueFiltered).2
    exact valueAbsent valueSecond
  calc
    decidableListUnion first second =
        decidableListUnion
          (first.filter fun value => decide (value ∉ second)) second :=
      unionFilter
    _ = (first.filter fun value => decide (value ∉ second)).dedup ++
        second := by
      exact filteredDisjoint.union_eq

end PeriodicThreeSATThree
end LeanTrominoes
