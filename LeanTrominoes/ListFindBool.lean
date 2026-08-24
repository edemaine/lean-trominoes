/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Small Boolean list-lookup laws -/

namespace LeanTrominoes

/-- A Boolean search returns none when its predicate is false on every list
member. -/
theorem listFind?_eq_none_of_forall_false
    {Value : Type*} (values : List Value) (predicate : Value → Bool)
    (falseOn : ∀ value ∈ values, predicate value = false) :
    values.find? predicate = none := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have valueFalse := falseOn value (by simp)
      have tailFalse : ∀ item ∈ values, predicate item = false := by
        intro item itemMember
        exact falseOn item (by simp [itemMember])
      simp [List.find?, valueFalse, induction tailFalse]

/-- Appending values rejected by a Boolean predicate does not change its
first successful lookup. -/
theorem listFind?_append_of_right_forall_false
    {Value : Type*} (first second : List Value)
    (predicate : Value → Bool)
    (falseOnSecond : ∀ value ∈ second, predicate value = false) :
    (first ++ second).find? predicate = first.find? predicate := by
  induction first with
  | nil =>
      simpa using
        listFind?_eq_none_of_forall_false second predicate falseOnSecond
  | cons value first induction =>
      by_cases selected : predicate value = true
      · simp [List.find?, selected]
      · have rejected : predicate value = false :=
          by
            cases valueEq : predicate value with
            | false => rfl
            | true => exact (selected valueEq).elim
        simp [List.find?, rejected, induction]

/-- Pointwise-equal Boolean predicates have equal first-successful lookups. -/
theorem listFind?_congr_of_forall_mem
    {Value : Type*} (values : List Value)
    (first second : Value → Bool)
    (equalOn : ∀ value ∈ values, first value = second value) :
    values.find? first = values.find? second := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have headEqual := equalOn value (by simp)
      have tailEqual : ∀ item ∈ values, first item = second item := by
        intro item itemMember
        exact equalOn item (by simp [itemMember])
      by_cases selected : second value = true
      · have firstSelected : first value = true := headEqual.trans selected
        simp [List.find?, selected, firstSelected]
      · have secondRejected : second value = false :=
          by
            cases valueEq : second value with
            | false => rfl
            | true => exact (selected valueEq).elim
        have firstRejected : first value = false :=
          headEqual.trans secondRejected
        simp [List.find?, secondRejected, firstRejected,
          induction tailEqual]

end LeanTrominoes
