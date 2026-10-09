/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.Count

/-! # Boolean coherence characterized by the number of true entries -/
namespace LeanTrominoes

theorem bool_count_length_of_all_true (values : List Bool) (all : ∀ value ∈ values, value=true) :
    values.count true=values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    have head := all value (by simp)
    have tail := ih (fun other member => all other (List.mem_cons_of_mem _ member))
    simp [head,tail]

theorem bool_all_true_of_count_length (values : List Bool) (count : values.count true=values.length) :
    ∀ value ∈ values, value=true := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    cases value with
    | false =>
      have bound : rest.count true ≤ rest.length := List.count_le_length
      change rest.count true=rest.length+1 at count
      omega
    | true =>
      have tail : rest.count true=rest.length := by simpa using count
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact ih tail other member

theorem bool_coherent_iff_count (values : List Bool) :
    (∀ first ∈ values, ∀ second ∈ values, first=second) ↔
      values.count true=0 ∨ values.count true=values.length := by
  constructor
  · intro coherent
    by_cases present : true ∈ values
    · exact Or.inr (bool_count_length_of_all_true values (fun value member => (coherent true present value member).symm))
    · exact Or.inl (List.count_eq_zero.mpr present)
  · intro count first firstMember second secondMember
    rcases count with zero | full
    · have allFalse (value : Bool) (member : value ∈ values) : value=false := by
        cases value with
        | false => rfl
        | true => exact False.elim ((List.count_eq_zero.mp zero) member)
      rw [allFalse first firstMember,allFalse second secondMember]
    · rw [bool_all_true_of_count_length values full first firstMember,
        bool_all_true_of_count_length values full second secondMember]

end LeanTrominoes
