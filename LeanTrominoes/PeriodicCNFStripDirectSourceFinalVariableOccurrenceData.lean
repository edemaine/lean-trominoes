/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedVariableOccurrenceCompiler

/-! # Completed endpoint records supplied to direct variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directVariableOccurrenceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One variable-side occurrence record per completed route, with the
departure direction taken from its reversed last edge. -/
def directSourceFinalVariableOccurrenceData (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.OccurrenceData :=
  HorizontalRoutedVariableOccurrence.output
    (directSourceFinalCompiledRouteTailRecords decider symbols)

noncomputable def directSourceFinalVariableOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalVariableOccurrenceData decider) := by
  unfold directSourceFinalVariableOccurrenceData
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
    HorizontalRoutedVariableOccurrence.computableInPolyTime

theorem directSourceFinalVariableOccurrenceData_eq_routePairs
    (symbols : List encoding.Γ) :
    directSourceFinalVariableOccurrenceData decider symbols =
      (directFigureNinePolarityRoutePairs decider symbols).map fun pair =>
        HorizontalRoutedRouteHeader.completeOccurrenceData pair.1 pair.2 := by
  unfold directSourceFinalVariableOccurrenceData
  rw [directSourceFinalCompiledRouteTailRecords_eq,
    directFigureNinePolarityRouteTailRecords_eq_records,
    HorizontalRoutedVariableOccurrence.output_records]

/-- Correcting the endpoint direction preserves the occurrence alignment. -/
@[simp] theorem directSourceFinalVariableOccurrenceData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalVariableOccurrenceData_eq_routePairs,
    directSourceFinalCompiledOccurrenceData_eq_routePairs]
  simp

/-- Endpoint correction leaves the connector-kind column unchanged. -/
theorem directSourceFinalVariableOccurrenceData_map_kind
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).map
        HorizontalRoutedRouteHeader.OccurrenceData.kind =
      (directSourceFinalCompiledOccurrenceData decider symbols).map
        HorizontalRoutedRouteHeader.OccurrenceData.kind := by
  rw [directSourceFinalVariableOccurrenceData_eq_routePairs,
    directSourceFinalCompiledOccurrenceData_eq_routePairs]
  simp

end LeanTrominoes.PeriodicCNFStripReduction

end
