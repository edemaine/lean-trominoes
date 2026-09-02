/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourAlignedFlatten
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceParentElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanKindSemantics

/-! # Occurrence semantics of expected parent-terminal element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The parent-selector component of the audited variable-incidence blocks
is exactly the RGB terminal block of each aligned grouped occurrence. -/
theorem directSourceFinalExpectedParentIncidenceElementCodes_eq_grouped
    (symbols : List encoding.Γ) :
    directSourceFinalExpectedParentIncidenceElementCodes decider symbols =
      directSourceFinalGroupedOccurrenceParentElementCodes
        decider symbols := by
  unfold directSourceFinalExpectedParentIncidenceElementCodes
    directSourceFinalGroupedOccurrenceParentElementCodes
  apply List.zipWith4_flatten_eq_zipWith_flatten_of_forall₂
    (fun pair data =>
      pair.1.kind (groupedVariableFanSiteSlot pair.2) = data.kind)
    groupedVariableIncidenceExpectedParentElementCodeBlock
    finalOccurrenceParentElementCodeBlock
    (directSourceFinalGroupedVariableFanSlotKinds decider symbols)
  · exact directSourceFinalGroupedVariableFanSlots_length decider symbols
  · rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedNextOccurrenceKeys_length]
  · rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedParentIndices_length]
  · intro pair data current next parent kindEq
    exact groupedVariableIncidenceExpectedParentElementCodeBlock_eq_of_kind_eq
      pair data current next parent kindEq

/-- Therefore the audited grouped parent contribution is a permutation of
the complete clause-major occurrence-derived terminal stream. -/
theorem directSourceFinalExpectedParentIncidenceElementCodes_perm
    (symbols : List encoding.Γ) :
    (directSourceFinalExpectedParentIncidenceElementCodes
        decider symbols).Perm
      (directSourceFinalOccurrenceParentElementCodes decider symbols) := by
  rw [directSourceFinalExpectedParentIncidenceElementCodes_eq_grouped]
  exact directSourceFinalGroupedOccurrenceParentElementCodes_perm
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
