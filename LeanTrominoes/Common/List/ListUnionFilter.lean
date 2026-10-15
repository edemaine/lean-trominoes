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

/-- The canonical decision procedure for absence from a list. -/
def decidableListAbsentDecision
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (value : Value) : Decidable (value ∉ values) :=
  inferInstance

/-- Boolean absence test induced by the same selected decidable equality. -/
def decidableListAbsent {Value : Type*} [DecidableEq Value]
    (values : List Value) (value : Value) : Bool :=
  @decide (value ∉ values)
    (decidableListAbsentDecision values value)

/-- The Boolean result of the canonical absence test is independent of the
correct decision procedure used for its proposition. -/
theorem decidableListAbsent_eq_decide
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (value : Value)
    (decision : Decidable (value ∉ values)) :
    decidableListAbsent values value =
      @decide (value ∉ values) decision := by
  unfold decidableListAbsent
  have decisionsEqual :
      decidableListAbsentDecision values value = decision :=
    Subsingleton.elim _ _
  exact congrArg
    (fun choice : Decidable (value ∉ values) =>
      @decide (value ∉ values) choice)
    decisionsEqual

/-- Canonical list union retains the deduplicated entries of its first
argument that are absent from its second argument, followed by the second
argument unchanged. -/
theorem decidableListUnion_eq_filteredDedup_append
    {Value : Type*} [DecidableEq Value]
    (first second : List Value) :
    decidableListUnion first second =
      (first.filter (decidableListAbsent second)).dedup ++
        second := by
  have unionFilter :
      decidableListUnion first second =
        decidableListUnion
          (first.filter (decidableListAbsent second)) second := by
    induction first with
    | nil => rfl
    | cons value rest induction =>
        unfold decidableListUnion at induction ⊢
        by_cases valueMember : value ∈ second
        · rw [List.filter_cons_of_neg
            (by simp [decidableListAbsent, valueMember])]
          have valueUnion :
              value ∈
                @List.union Value instBEqOfDecidableEq rest second := by
            exact List.mem_union_right rest valueMember
          change List.insert value
              (@List.union Value instBEqOfDecidableEq rest second) =
            @List.union Value instBEqOfDecidableEq
              (rest.filter (decidableListAbsent second)) second
          rw [List.insert_of_mem valueUnion]
          exact induction
        · rw [List.filter_cons_of_pos
            (by simp [decidableListAbsent, valueMember])]
          change List.insert value
              (@List.union Value instBEqOfDecidableEq rest second) =
            List.insert value
              (@List.union Value instBEqOfDecidableEq
                (rest.filter (decidableListAbsent second)) second)
          exact congrArg (List.insert value) induction
  have filteredDisjoint :
      List.Disjoint
        (first.filter (decidableListAbsent second)) second := by
    rw [List.disjoint_left]
    intro value valueFiltered valueSecond
    have valueAbsent : value ∉ second := by
      simpa only [decidableListAbsent, decide_eq_true_eq] using
        (List.mem_filter.mp valueFiltered).2
    exact valueAbsent valueSecond
  calc
    decidableListUnion first second =
        decidableListUnion
          (first.filter (decidableListAbsent second)) second :=
      unionFilter
    _ = (first.filter (decidableListAbsent second)).dedup ++
        second := by
      exact filteredDisjoint.union_eq

end PeriodicThreeSATThree
end LeanTrominoes
