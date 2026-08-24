/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SupportedLastRepresentativeEqualityRowSelection
import Mathlib.Data.List.Dedup

/-! # Semantics of support-guarded last-representative rows -/

namespace LeanTrominoes.SupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Guarded row selection over a suffix implements last-occurrence dedup and
support filtering while preserving each selected augmented equality row. -/
theorem rowsAux_rows_append
    (base before remaining : List Value) :
    LastRepresentativeEqualityRows.rowsAux before.length
        (remaining.map (row base (before ++ remaining))) =
      ((remaining.dedup.filter fun value => value ∈ base).map
        (row base (before ++ remaining))) := by
  induction remaining generalizing before with
  | nil => simp
  | cons value remaining induction =>
      by_cases later : value ∈ remaining
      · have selectedFalse :
            LastRepresentativeEqualityRows.selected before.length
                (row base (before ++ value :: remaining) value) = false := by
          rw [selected_row_append]
          simp [later]
        rw [List.map_cons,
          LastRepresentativeEqualityRows.rowsAux_cons_rejected
            _ _ _ selectedFalse,
          List.dedup_cons_of_mem later]
        simpa [List.append_assoc] using
          induction (before ++ [value])
      · by_cases supported : value ∈ base
        · have selectedTrue :
              LastRepresentativeEqualityRows.selected before.length
                  (row base (before ++ value :: remaining) value) = true := by
            rw [selected_row_append]
            simp [later, supported]
          rw [List.map_cons,
            LastRepresentativeEqualityRows.rowsAux_cons_selected
              _ _ _ selectedTrue,
            List.dedup_cons_of_notMem later]
          simp only [List.filter_cons]
          simp [supported]
          simpa [List.append_assoc] using
            induction (before ++ [value])
        · have selectedFalse :
              LastRepresentativeEqualityRows.selected before.length
                  (row base (before ++ value :: remaining) value) = false := by
            rw [selected_row_append]
            simp [supported]
          rw [List.map_cons,
            LastRepresentativeEqualityRows.rowsAux_cons_rejected
              _ _ _ selectedFalse,
            List.dedup_cons_of_notMem later]
          simp only [List.filter_cons]
          simp [supported]
          simpa [List.append_assoc] using
            induction (before ++ [value])

/-- Applying the existing last-representative machine semantics to guarded
rows yields stable supported representatives exactly. -/
theorem selectedRows_eq
    (base candidates : List Value) :
    selectedRows base candidates =
      ⟨((candidates.dedup.filter fun value => value ∈ base).map
        (row base candidates))⟩ := by
  unfold selectedRows rows LastRepresentativeEqualityRows.rows
  congr 1
  exact rowsAux_rows_append base [] candidates

end LeanTrominoes.SupportedLastRepresentativeEqualityRows
