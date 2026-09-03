/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalColumns

/-! # Validity of grouped variable-incidence source columns -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every aligned start/data pair has routed-key membership local to its
complete occurrence interval. -/
theorem directSourceFinalGroupedVariableIncidenceIntervals_local
    (symbols : List encoding.Γ) :
    List.Forall₂
      (GroupedVariableIncidenceLocalColumn.IntervalLocal
        (directSourceFinalGroupedRoutedIncidenceKeys decider symbols))
      (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
      (directSourceFinalGroupedOccurrenceData decider symbols) := by
  apply List.forall₂_of_length_eq_of_get
    (directSourceFinalGroupedOccurrenceTripleBlockStarts_length
      decider symbols)
  intro index startsIndexLt dataIndexLt
  intro query lower upper
  have startEq :
      directSourceFinalGroupedOccurrenceTripleBlockStartAt
          decider symbols index =
        (directSourceFinalGroupedOccurrenceTripleBlockStarts
          decider symbols).get ⟨index, startsIndexLt⟩ := by
    unfold directSourceFinalGroupedOccurrenceTripleBlockStartAt
    rw [List.getD_eq_getElem _ _ startsIndexLt]
    simp only [List.get_eq_getElem]
  have dataEq :
      directSourceFinalGroupedOccurrenceDataAt decider symbols index =
        (directSourceFinalGroupedOccurrenceData decider symbols).get
          ⟨index, dataIndexLt⟩ := by
    unfold directSourceFinalGroupedOccurrenceDataAt
    rw [List.getD_eq_getElem _ _ dataIndexLt]
    simp only [List.get_eq_getElem]
  rw [← startEq] at lower upper ⊢
  rw [← dataEq] at upper ⊢
  exact directSourceFinalGroupedRoutedIncidenceKey_mem_iff_local
    decider symbols index query dataIndexLt lower upper

/-- Every concrete four-field source column meets the generic localization
invariant. -/
theorem directSourceFinalGroupedVariableIncidenceLocalColumns_valid
    (symbols : List encoding.Γ) :
    ∀ column ∈
        directSourceFinalGroupedVariableIncidenceLocalColumns decider symbols,
      column.Valid
        (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
        (directSourceFinalGroupedColoredOccurrenceDirectionBodies
          decider symbols) := by
  unfold directSourceFinalGroupedVariableIncidenceLocalColumns
  exact GroupedVariableIncidenceLocalColumn.valid_of_forall₂_alignments
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)
    (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedOccurrenceDirectionBodyBlocks decider symbols)
    (directSourceFinalGroupedVariableFanSlotKinds decider symbols)
    (directSourceFinalGroupedRoutedIncidenceBodyBlocks_aligned_localColumns
      decider symbols)
    (directSourceFinalGroupedVariableIncidenceIntervals_local decider symbols)

/-- The complete flattened global source-column presentation equals its
occurrence-local presentation. -/
theorem
    directSourceFinalGroupedVariableIncidenceGlobalBodyBlocks_eq_localBodyBlocks
    (symbols : List encoding.Γ) :
    ((directSourceFinalGroupedVariableIncidenceLocalColumns
      decider symbols).map
        (GroupedVariableIncidenceLocalColumn.globalBodyBlock
          (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
          (directSourceFinalGroupedColoredOccurrenceDirectionBodies
            decider symbols))).flatten =
      ((directSourceFinalGroupedVariableIncidenceLocalColumns
        decider symbols).map
          GroupedVariableIncidenceLocalColumn.localBodyBlock).flatten := by
  exact
    GroupedVariableIncidenceLocalColumn.flatten_map_globalBodyBlock_eq_localBodyBlock
      (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
      (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)
      (directSourceFinalGroupedVariableIncidenceLocalColumns decider symbols)
      (directSourceFinalGroupedVariableIncidenceLocalColumns_valid
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
