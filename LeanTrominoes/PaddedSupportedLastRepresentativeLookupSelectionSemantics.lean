/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics
import LeanTrominoes.PaddedSupportedLastRepresentativeSelectionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupTrailingFalseSemantics

/-! # Unary lookup through selected support-guarded rows -/

namespace LeanTrominoes
namespace PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Looking up a key-derived unary datum through the selected guarded rows
returns that datum once for every stable supported optional value. -/
theorem lookups_selectedRows_map
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (datum : Option Value → Nat) :
    LastTrueUnaryValueLookupMachine.lookups
        (selectedRows candidates).words
        ((values candidates).map datum) =
      (((values candidates).dedup.filter fun value =>
        value ∈ base.map some).map datum) := by
  rw [selectedRows_eq base candidates correct]
  unfold LastTrueUnaryValueLookupMachine.lookups
  rw [List.map_map]
  apply List.map_congr_left
  intro value valueMember
  have candidateMember : value ∈ values candidates := by
    simpa using (List.mem_filter.mp valueMember).1
  have supported : value ∈ base.map some :=
    of_decide_eq_true (List.mem_filter.mp valueMember).2
  simp only [Function.comp_apply]
  unfold SupportedLastRepresentativeEqualityRows.row
  have selected :=
    LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
      datum (values candidates) value candidateMember
  unfold LastTrueUnaryValueLookupMachine.lookup at selected ⊢
  simp only [supported, not_true_eq_false, decide_false]
  rw [LastTrueUnaryValueLookupMachine.lookupAux_append_false_of_length_eq]
  · simpa [LastRepresentativeEqualityRows.equalityRow,
      StableOccurrenceRanks.equalityRow] using selected
  · simp [LastRepresentativeEqualityRows.equalityRow]

end PaddedSupportedLastRepresentativeEqualityRows
end LeanTrominoes
