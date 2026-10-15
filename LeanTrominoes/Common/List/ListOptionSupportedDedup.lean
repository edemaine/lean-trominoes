/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Supported stable deduplication of optional values -/

namespace List

variable {Value : Type*} [BEq Value] [LawfulBEq Value]
  [DecidableEq Value]

/-- Filtering commutes with stable deduplication while using the caller's
lawful Boolean equality throughout. -/
private theorem dedup_filter_beq
    (predicate : Value → Bool) (values : List Value) :
    (values.filter predicate).dedup =
      values.dedup.filter predicate := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases selected : predicate value <;>
        by_cases later : value ∈ values <;>
          simp [selected, later, induction]

/-- Stable deduplication commutes with the injective `some` constructor
under the inherited option equality. -/
private theorem dedup_map_some (values : List Value) :
    (values.map some).dedup = values.dedup.map some := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases later : value ∈ values <;>
        simp [later, induction]

omit [DecidableEq Value] in
/-- Filtering optional values by membership in a lifted base list is exactly
filtering their present values before reattaching `some`. -/
theorem filter_mem_map_some_eq
    (base : List Value) (options : List (Option Value)) :
    options.filter (fun option => decide (option ∈ base.map some)) =
      ((options.filterMap id).filter fun value =>
        decide (value ∈ base)).map some := by
  induction options with
  | nil => rfl
  | cons option options induction =>
      cases option with
      | none =>
          have rejected : decide (none ∈ base.map some) = false := by
            simp
          simp only [List.filter_cons, rejected, Bool.false_eq_true,
            ↓reduceIte]
          change
            options.filter
                (fun option => decide (option ∈ base.map some)) =
              ((options.filterMap id).filter fun value =>
                decide (value ∈ base)).map some
          exact induction
      | some value =>
          have filterMapCons :
              (some value :: options).filterMap id =
                value :: options.filterMap id := by
            rfl
          by_cases member : value ∈ base
          · have accepted :
                decide (some value ∈ base.map some) = true := by
              simp [member]
            have acceptedValue : decide (value ∈ base) = true := by
              simp [member]
            simp only [List.filter_cons, accepted, ↓reduceIte,
              filterMapCons, acceptedValue, List.map_cons]
            exact congrArg (List.cons (some value)) induction
          · have rejected :
                decide (some value ∈ base.map some) = false := by
              simp [member]
            have rejectedValue : decide (value ∈ base) = false := by
              simp [member]
            simp only [List.filter_cons, rejected, Bool.false_eq_true,
              ↓reduceIte, filterMapCons, rejectedValue]
            exact induction

/-- Inactive optional slots do not affect the stable order of supported
present values. -/
theorem dedup_filter_mem_map_some_eq
    (base : List Value) (options : List (Option Value)) :
    options.dedup.filter
        (fun option => decide (option ∈ base.map some)) =
      (((options.filterMap id).dedup.filter fun value =>
        decide (value ∈ base)).map some) := by
  rw [← dedup_filter_beq]
  rw [filter_mem_map_some_eq]
  rw [dedup_map_some]
  rw [dedup_filter_beq]

end List
