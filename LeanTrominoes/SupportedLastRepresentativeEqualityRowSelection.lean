/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SupportedLastRepresentativeEqualityRows

/-! # Selection semantics of one support-guarded equality row -/

namespace LeanTrominoes.SupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- A guarded row is selected exactly when its value has no later occurrence
and belongs to the supported base set. -/
theorem selected_row_append
    (base before : List Value) (value : Value) (after : List Value) :
    LastRepresentativeEqualityRows.selected before.length
        (row base (before ++ value :: after) value) =
      decide (value ∉ after ∧ value ∈ base) := by
  have dropEq :
      (row base (before ++ value :: after) value).drop
          (before.length + 1) =
        after.map (fun other => decide (value = other)) ++
          [decide (value ∉ base)] := by
    have dropPrefix (bits suffix : List Bool) :
        (bits ++ true :: suffix).drop (bits.length + 1) = suffix := by
      induction bits with
      | nil => rfl
      | cons bit bits induction =>
          simp [induction]
    unfold row LastRepresentativeEqualityRows.equalityRow
    simpa [List.map_append] using
      dropPrefix
        (before.map fun other => decide (value = other))
        (after.map (fun other => decide (value = other)) ++
          [decide (value ∉ base)])
  unfold LastRepresentativeEqualityRows.selected
  rw [dropEq]
  by_cases later : value ∈ after <;>
    by_cases supported : value ∈ base <;>
      simp [later, supported]

end LeanTrominoes.SupportedLastRepresentativeEqualityRows
