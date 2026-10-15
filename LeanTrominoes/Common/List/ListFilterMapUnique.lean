/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Filtering a unique selected list value -/

namespace List

/-- Selecting a value absent from a list gives an empty `filterMap`. -/
theorem filterMap_eq_nil_of_target_not_mem
    {Value Output : Type*} [DecidableEq Value]
    (values : List Value) (target : Value) (output : Output)
    (targetNotMem : target ∉ values) :
    values.filterMap (fun value =>
        if value = target then some output else none) = [] := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.mem_cons, not_or] at targetNotMem
      have headNe : head ≠ target :=
        fun equal => targetNotMem.1 equal.symm
      simp [headNe, induction targetNotMem.2]

/-- A duplicate-free list contributes exactly one constant output when
filtering for one of its values. -/
theorem filterMap_eq_singleton_of_nodup
    {Value Output : Type*} [DecidableEq Value]
    (values : List Value) (target : Value) (output : Output)
    (nodup : values.Nodup) (targetMem : target ∈ values) :
    values.filterMap (fun value =>
        if value = target then some output else none) = [output] := by
  induction values with
  | nil => simp at targetMem
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      simp only [List.mem_cons] at targetMem
      rcases targetMem with targetEq | targetTail
      · subst target
        have tailNil := filterMap_eq_nil_of_target_not_mem
          tail head output nodup.1
        simp [tailNil]
      · have headNe : head ≠ target := by
          intro equal
          exact nodup.1 (equal ▸ targetTail)
        simp [headNe, induction nodup.2 targetTail]

/-- Concatenating optional singleton blocks is the corresponding filtered
map. -/
theorem flatMap_eq_filter_map_of_eq_if
    {Value Output : Type*}
    (values : List Value) (predicate : Value → Bool)
    (output : Value → Output) (block : Value → List Output)
    (blockEq : ∀ value ∈ values,
      block value = if predicate value then [output value] else []) :
    values.flatMap block = (values.filter predicate).map output := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headEq := blockEq head (List.mem_cons_self)
      have tailEq : ∀ value ∈ tail,
          block value = if predicate value then [output value] else [] := by
        intro value valueMem
        exact blockEq value (List.mem_cons_of_mem head valueMem)
      cases accepted : predicate head
      · simp [headEq, accepted, induction tailEq]
      · simp [headEq, accepted, induction tailEq]

end List
