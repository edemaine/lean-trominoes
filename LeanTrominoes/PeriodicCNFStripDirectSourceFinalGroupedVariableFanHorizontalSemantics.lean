/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceEntryOrder
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanHorizontalSemantics

/-! # Complete fan/slot semantics in canonical horizontal occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedFanHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- The finite compiled slot at a semantic occurrence's recovered position
is exactly that entry's active slot. -/
theorem directSourceFinalOccurrenceSlot_getD_eq_entry
    (symbols : List encoding.Γ) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) :
    (directSourceFinalOccurrenceSlots decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) default = entry.2 := by
  let positioned := horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have spec := occurrenceEntryIndex_spec positioned.erase entry member
  have indexLt := (List.getElem?_eq_some_iff.mp spec.1).1
  unfold directSourceFinalOccurrenceSlots BoundedOccurrenceSlots.slots
  have ranksEq : directSourceFinalOccurrenceStableRanks decider symbols =
      StableOccurrenceRanks.ranks positioned.erase.variableOccurrences := by
    rw [directSourceFinalOccurrenceStableRanks_eq_identityCodes]
    have lengths : (directSourceFinalAtomIdentityCodes decider symbols).length =
        positioned.erase.variableOccurrences.length := by
      rw [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms]
      exact (congrArg List.length (horizontalSemanticNormalizedRibbonSource_variableOccurrences _)).symm
    apply StableOccurrenceRanks.ranks_eq_of_partition _ _ lengths
    intro first second firstLt secondLt
    simpa only [positioned, horizontalSemanticNormalizedRibbonSource_variableOccurrences] using
      directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols first second firstLt secondLt
  rw [ranksEq]
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt), List.getElem_map]
  have rankEq := spec.2
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt)] at rankEq
  rw [rankEq]
  cases entry.2 <;> rfl

/-- The complete grouped fan/slot stream agrees with the actual normalized
source entry order, with each fan and active slot attached to its own atom. -/
theorem directSourceFinalGroupedVariableFanSlots_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlots decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (fun entry =>
          (horizontalOccurrenceVariableRibbonFanDataComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1),
          groupedVariableFanGenericSlot entry.2)) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_map_getD,
    directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries, List.map_map]
  apply List.map_congr_left
  intro entry member
  have spec := occurrenceEntryIndex_spec (horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry member
  apply Prod.ext
  · have identified := directSourceFinalVariableFanData_getD_eq_horizontal decider symbols
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) entry.1 spec.1
    have fanLt : occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry <
        (directSourceFinalVariableFanData decider symbols).length := by
      rw [directSourceFinalVariableFanData_length, ← directSourceFinalAtomIdentityCodes_length,
        directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms,
        ← horizontalSemanticNormalizedRibbonSource_variableOccurrences]
      exact (List.getElem?_eq_some_iff.mp spec.1).1
    simpa only [Function.comp_apply, List.getD_eq_getElem _ _ fanLt] using identified
  · exact congrArg groupedVariableFanGenericSlot
      (directSourceFinalOccurrenceSlot_getD_eq_entry decider symbols entry member)

end LeanTrominoes.PeriodicCNFStripReduction

end
