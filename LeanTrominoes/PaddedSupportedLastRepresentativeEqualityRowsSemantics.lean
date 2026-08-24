/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Semantics of fixed-slot guarded equality rows -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Under the support invariant, a slot's negated tag is exactly the
membership-rejection bit expected by guarded representative rows. -/
theorem not_supported_eq_not_mem
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (candidate : Candidate Value) (member : candidate ∈ candidates) :
    (!candidate.supported) =
      decide (candidate.value ∉ base.map some) := by
  rw [correct candidate member]
  by_cases supported : candidate.value ∈ base.map some <;>
    simp [supported]

/-- Correctly tagged fixed slots are exactly ordinary support-guarded rows
over their option-valued presentation stream. -/
theorem rows_eq_supportedRows
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    rows candidates =
      SupportedLastRepresentativeEqualityRows.rows
        (base.map some) (values candidates) := by
  unfold rows SupportedLastRepresentativeEqualityRows.rows values
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate member
  unfold row SupportedLastRepresentativeEqualityRows.row
  rw [not_supported_eq_not_mem base candidates correct candidate member]
  simp [values, Function.comp_apply]

/-- The existing selector therefore acts on fixed slots exactly as it acts
on the corresponding support-guarded option rows. -/
theorem selectedRows_eq_supportedSelectedRows
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    selectedRows candidates =
      SupportedLastRepresentativeEqualityRows.selectedRows
        (base.map some) (values candidates) := by
  unfold selectedRows
    SupportedLastRepresentativeEqualityRows.selectedRows
  rw [rows_eq_supportedRows base candidates correct]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
