/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeOccurrences
import Mathlib.Data.List.Dedup

/-! # Exact distinct counts for sum-typed variable lists -/

namespace LeanTrominoes
namespace PeriodicOneInThree
namespace SumVariableCount

@[simp] theorem inl_mem_iff {Original Auxiliary : Type*}
    (atom : Original) (entries : List (Sum Original Auxiliary)) :
    Sum.inl atom ∈ entries ↔ atom ∈ originalVariables entries := by
  induction entries with
  | nil => simp [originalVariables]
  | cons head rest induction =>
      cases head <;> simp_all [originalVariables]

@[simp] theorem inr_mem_iff {Original Auxiliary : Type*}
    (atom : Auxiliary) (entries : List (Sum Original Auxiliary)) :
    Sum.inr atom ∈ entries ↔ atom ∈ auxiliaryVariables entries := by
  induction entries with
  | nil => simp [auxiliaryVariables]
  | cons head rest induction =>
      cases head <;> simp_all [auxiliaryVariables]

@[simp] theorem originalVariables_append {Original Auxiliary : Type*}
    (first second : List (Sum Original Auxiliary)) :
    originalVariables (first ++ second) =
      originalVariables first ++ originalVariables second := by
  induction first with
  | nil => rfl
  | cons head rest induction =>
      cases head <;> simp [originalVariables, induction]

@[simp] theorem auxiliaryVariables_append {Original Auxiliary : Type*}
    (first second : List (Sum Original Auxiliary)) :
    auxiliaryVariables (first ++ second) =
      auxiliaryVariables first ++ auxiliaryVariables second := by
  induction first with
  | nil => rfl
  | cons head rest induction =>
      cases head <;> simp [auxiliaryVariables, induction]

/-- The distinct elements of a sum-typed list are exactly its distinct left
elements plus its distinct right elements. -/
theorem dedup_length_eq_original_add_auxiliary
    {Original Auxiliary : Type*}
    [DecidableEq Original] [DecidableEq Auxiliary]
    (entries : List (Sum Original Auxiliary)) :
    entries.dedup.length =
      (originalVariables entries).dedup.length +
        (auxiliaryVariables entries).dedup.length := by
  induction entries with
  | nil => rfl
  | cons head rest induction =>
      cases head with
      | inl atom =>
          simp only [originalVariables, auxiliaryVariables]
          by_cases member : Sum.inl atom ∈ rest
          · have originalMember : atom ∈ originalVariables rest :=
              (inl_mem_iff atom rest).mp member
            rw [List.dedup_cons_of_mem member,
              List.dedup_cons_of_mem originalMember]
            exact induction
          · have originalNotMember : atom ∉ originalVariables rest := by
              simpa using member
            rw [List.dedup_cons_of_notMem member,
              List.dedup_cons_of_notMem originalNotMember]
            simp only [List.length_cons]
            omega
      | inr atom =>
          simp only [originalVariables, auxiliaryVariables]
          by_cases member : Sum.inr atom ∈ rest
          · have auxiliaryMember : atom ∈ auxiliaryVariables rest :=
              (inr_mem_iff atom rest).mp member
            rw [List.dedup_cons_of_mem member,
              List.dedup_cons_of_mem auxiliaryMember]
            exact induction
          · have auxiliaryNotMember : atom ∉ auxiliaryVariables rest := by
              simpa using member
            rw [List.dedup_cons_of_notMem member,
              List.dedup_cons_of_notMem auxiliaryNotMember]
            simp only [List.length_cons]
            omega

end SumVariableCount
end PeriodicOneInThree
end LeanTrominoes
