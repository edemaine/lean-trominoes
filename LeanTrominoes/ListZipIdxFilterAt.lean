/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # Filtering an indexed list at one position -/

namespace List

/-- No index in `zipIdx start` is smaller than `start`. -/
theorem filter_zipIdx_eq_index_eq_nil_of_lt
    (values : List α) (start index : Nat) (indexLt : index < start) :
    (values.zipIdx start).filter (fun tagged =>
      decide (index = tagged.2)) = [] := by
  induction values generalizing start with
  | nil => rfl
  | cons value values induction =>
      simp only [List.zipIdx_cons, List.filter_cons]
      have indexNe : index ≠ start := by omega
      rw [show decide (index = start) = false by simp [indexNe]]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact induction (start + 1) (by omega)

/-- Filtering `zipIdx start` at `start + offset` returns exactly the indexed
element at `offset`, or the empty list when that element is absent. -/
theorem filter_zipIdx_eq_add_index
    (values : List α) (start offset : Nat) :
    (values.zipIdx start).filter (fun tagged =>
      decide (start + offset = tagged.2)) =
      match values[offset]? with
      | some value => [(value, start + offset)]
      | none => [] := by
  induction values generalizing start offset with
  | nil => rfl
  | cons value values induction =>
      cases offset with
      | zero =>
          simp only [Nat.add_zero, List.zipIdx_cons, List.filter_cons,
            List.getElem?_cons_zero, decide_true, ↓reduceIte]
          rw [filter_zipIdx_eq_index_eq_nil_of_lt
            values (start + 1) start (by omega)]
      | succ offset =>
          simp only [List.zipIdx_cons, List.filter_cons,
            List.getElem?_cons_succ]
          rw [show decide (start + (offset + 1) = start) = false by
            simp]
          rw [if_neg (by decide : ¬(false = true))]
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            induction (start + 1) offset

/-- At the default zero start, filtering by an index returns its unique
`zipIdx` entry when present. -/
theorem filter_zipIdx_eq_index (values : List α) (index : Nat) :
    values.zipIdx.filter (fun tagged => decide (index = tagged.2)) =
      match values[index]? with
      | some value => [(value, index)]
      | none => [] := by
  simpa using filter_zipIdx_eq_add_index values 0 index

end List
