/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRows
import Mathlib.Data.List.Dedup

/-! # Semantics of last-representative equality rows -/

namespace LeanTrominoes
namespace LastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

def equalityRow (values : List Value) (value : Value) : List Bool :=
  values.map fun other => decide (value = other)

def equalityRows (values : List Value) : List (List Bool) :=
  values.map (equalityRow values)

theorem selected_equalityRow_append (before : List Value) (value : Value)
    (after : List Value) :
    selected before.length
        (equalityRow (before ++ value :: after) value) =
      decide (value ∉ after) := by
  have dropEq :
      (equalityRow (before ++ value :: after) value).drop
          (before.length + 1) =
        after.map fun other => decide (value = other) := by
    unfold equalityRow
    rw [List.map_append, List.map_cons]
    induction before with
    | nil => simp
    | cons head before induction =>
        simp only [List.map_cons, List.length_cons]
        simpa [Nat.add_assoc] using induction
  by_cases member : value ∈ after
  · simp [selected, dropEq, member]
  · simp [selected, dropEq, member]

/-- Filtering full equality rows at their last occurrences is exactly Lean's
last-occurrence-preserving `List.dedup` order. -/
theorem rowsAux_equalityRows_append (before remaining : List Value) :
    rowsAux before.length
        (remaining.map (equalityRow (before ++ remaining))) =
      (remaining.dedup).map (equalityRow (before ++ remaining)) := by
  induction remaining generalizing before with
  | nil => simp
  | cons value remaining induction =>
      by_cases member : value ∈ remaining
      · have selectedFalse :
            selected before.length
                (equalityRow (before ++ value :: remaining) value) =
              false := by
            rw [selected_equalityRow_append]
            simp [member]
        rw [List.map_cons, rowsAux_cons_rejected _ _ _ selectedFalse,
          List.dedup_cons_of_mem member]
        simpa [List.append_assoc] using
          induction (before ++ [value])
      · have selectedTrue :
            selected before.length
                (equalityRow (before ++ value :: remaining) value) =
              true := by
            rw [selected_equalityRow_append]
            simp [member]
        rw [List.map_cons, rowsAux_cons_selected _ _ _ selectedTrue,
          List.dedup_cons_of_notMem member, List.map_cons]
        congr 1
        simpa [List.append_assoc] using
          induction (before ++ [value])

theorem rows_equalityRows (values : List Value) :
    rows ⟨equalityRows values⟩ = ⟨(values.dedup).map (equalityRow values)⟩ := by
  unfold rows equalityRows
  congr 1
  exact rowsAux_equalityRows_append [] values

end LastRepresentativeEqualityRows
end LeanTrominoes
