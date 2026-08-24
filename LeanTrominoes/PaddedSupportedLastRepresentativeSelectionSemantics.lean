/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRowsSemantics
import LeanTrominoes.SupportedLastRepresentativeEqualityRowsSemantics

/-! # Selection semantics of fixed candidate slots -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Fixed inactive gaps do not alter representative selection: the output is
stable deduplication of optional slot values followed by exact base support
filtering. -/
theorem selectedRows_eq
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    selectedRows candidates =
      ⟨(((values candidates).dedup.filter fun value =>
          value ∈ base.map some).map
        (SupportedLastRepresentativeEqualityRows.row
          (base.map some) (values candidates)))⟩ := by
  rw [selectedRows_eq_supportedSelectedRows base candidates correct]
  rw [SupportedLastRepresentativeEqualityRows.selectedRows_eq]
  congr 1
  apply congrArg (List.map
    (SupportedLastRepresentativeEqualityRows.row
      (base.map some) (values candidates)))
  apply List.filter_congr
  intro value _valueMember
  by_cases member : value ∈ base.map some <;>
    simp [member]

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
