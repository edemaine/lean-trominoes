/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameOccurrenceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameSemantics

/-! # Every field of an occurrence frame belongs to one actual source entry -/

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

noncomputable local instance occurrenceFrameFieldsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Declarative frames cover exactly the original occurrence stream. -/
@[simp] theorem directSourceFinalOccurrenceFramesExpected_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFramesExpected decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [← directSourceFinalOccurrenceFrames_eq_expected,
    directSourceFinalOccurrenceFrames_length]

/-- The variable fan, active slot, clause fan, and terminal group in one
compiled frame all refer to the same actual normalized source occurrence. -/
theorem directSourceFinalOccurrenceFrame_fields_of_occurrenceAt
    (symbols : List encoding.Γ) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2 = some tagged) :
    let frame := (directSourceFinalOccurrenceFramesExpected decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) default
    frame.variableFan = horizontalOccurrenceVariableRibbonFanDataComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1) ∧
      frame.occurrenceSlot = entry.2 ∧
      (frame.clauseFrame.clauseFan, frame.clauseFrame.group) =
        (horizontalOccurrenceClauseRibbonFanDataComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, tagged.2.1),
        terminalGroupOfLiteralIndex tagged.2.2) := by
  let positioned := horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  let index := occurrenceEntryIndex positioned.erase entry
  have spec := occurrenceEntryIndex_spec positioned.erase entry member
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalAtomIdentityCodes_length,
      directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms,
      ← horizontalSemanticNormalizedRibbonSource_variableOccurrences]
    exact (List.getElem?_eq_some_iff.mp spec.1).1
  have fanLt : index < (directSourceFinalVariableFanData decider symbols).length := by
    simpa using compiledLt
  have slotLt : index < (directSourceFinalOccurrenceSlots decider symbols).length := by
    simpa using compiledLt
  have clauseLt : index < (directSourceFinalClauseFrames decider symbols).length := by
    simpa using compiledLt
  have frameEq : (directSourceFinalOccurrenceFramesExpected decider symbols).getD index default =
      ({ variableFan := (directSourceFinalVariableFanData decider symbols).getD index default
         occurrenceSlot := (directSourceFinalOccurrenceSlots decider symbols).getD index default
         clauseFrame := (directSourceFinalClauseFrames decider symbols).getD index default } :
        DirectFinalOccurrenceFrame.Data) := by
    unfold directSourceFinalOccurrenceFramesExpected
    rw [List.getD_eq_getElem _ _ (by
      simp only [List.length_map, List.length_zip]; omega)]
    simp only [List.getElem_map, List.getElem_zip,
      List.getD_eq_getElem _ _ fanLt, List.getD_eq_getElem _ _ slotLt,
      List.getD_eq_getElem _ _ clauseLt]
  change let frame := (directSourceFinalOccurrenceFramesExpected decider symbols).getD index default; _
  rw [frameEq]
  dsimp only
  refine ⟨?_, directSourceFinalOccurrenceSlot_getD_eq_entry decider symbols entry member, ?_⟩
  · have identified := directSourceFinalVariableFanData_getD_eq_horizontal decider symbols index entry.1 spec.1
    simpa only [List.getD_eq_getElem _ _ fanLt] using identified
  · have identified := directSourceFinalClauseFrame_fields_of_occurrenceAt decider symbols
      entry.1 entry.2 tagged lookup
    dsimp only at identified
    exact identified

end LeanTrominoes.PeriodicCNFStripReduction

end
