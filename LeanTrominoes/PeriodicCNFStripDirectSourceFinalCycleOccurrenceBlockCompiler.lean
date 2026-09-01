/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFigureNineCycleRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockSemantics
import LeanTrominoes.TM2CompositionMachine

/-! # Direct implication-cycle occurrence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCycleOccurrenceBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCycleOccurrenceBlockVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Final occurrence data obtained from the constant record block emitted for
each retained-variable marker. -/
def directSourceFinalCycleOccurrenceData
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.OccurrenceData :=
  HorizontalRoutedRouteHeaderOccurrence.output
    (HorizontalRoutedRouteTailRecord.batchedRecords
      (directFigureNineCycleRouteTailRecordTokensCompiled decider symbols))

/-- The cycle occurrence stream is polynomial-time computable by composing
the marker-block record emitter, bounded record expansion, and header
projection. -/
noncomputable def directSourceFinalCycleOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCycleOccurrenceData decider) := by
  unfold directSourceFinalCycleOccurrenceData
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directFigureNineCycleRouteTailRecordTokensCompiledComputableInPolyTime
        decider)
      HorizontalRoutedRouteTailRecord.batchedRecordsComputableInPolyTime)
    HorizontalRoutedRouteHeaderOccurrence.computableInPolyTime

/-- One retained-variable marker also expands to the parent-relative atom
equality squares of all nine implication-ring clauses. -/
def directSourceFinalCycleAtomEqualityBlock :
    FormulaShapeDirectionOrdering.Token → List Bool
  | .variable =>
      HorizontalRoutedRouteHeaderOccurrenceBlock.atomEqualityBits
        FormulaShapeFixedEightDirection.cycleClauseDescriptors
  | .clause _ => []

/-- Block-local atom equalities for the complete implication-cycle suffix. -/
def directSourceFinalCycleLocalAtomEqualityBits
    (symbols : List encoding.Γ) : List Bool :=
  (directRetainedFigureNineFiniteSourceVariableMarkers
      decider symbols).flatMap directSourceFinalCycleAtomEqualityBlock

/-- All implication-cycle block-local atom equalities are polynomial-time. -/
noncomputable def
    directSourceFinalCycleLocalAtomEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCycleLocalAtomEqualityBits decider) := by
  unfold directSourceFinalCycleLocalAtomEqualityBits
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineFiniteSourceVariableMarkersComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      directSourceFinalCycleAtomEqualityBlock)

/-- The fixed local equality stream compares exactly the represented
parent-relative atoms in each implication-ring clause. -/
theorem directSourceFinalCycleAtomEqualityBlock_variable_eq :
    directSourceFinalCycleAtomEqualityBlock .variable =
      FormulaShapeFixedEightDirection.cycleClauseDescriptors.flatMap
        HorizontalRoutedRouteHeaderOccurrenceBlock.representedAtomEqualityBlock := by
  unfold directSourceFinalCycleAtomEqualityBlock
    HorizontalRoutedRouteHeaderOccurrenceBlock.atomEqualityBits
  apply List.flatMap_congr
  intro token _
  exact HorizontalRoutedRouteHeaderOccurrenceBlock.atomEqualityBlock_eq token

/-- Projecting one constant implication-ring record block gives exactly the
occurrence expansion of its nine finite clause descriptors. -/
theorem directSourceFinalCycleLocalRecordOccurrenceData_eq :
    HorizontalRoutedRouteHeaderOccurrence.output
        (HorizontalRoutedRouteTailRecord.batchedRecords
          FormulaShapeRetainedFigureNineCycleTail.localRecordTokens) =
      HorizontalRoutedRouteHeaderOccurrenceBlock.output
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  unfold FormulaShapeRetainedFigureNineCycleTail.localRecordTokens
  rw [HorizontalRoutedRouteHeaderOccurrenceBlock.occurrenceOutput_batchedRecords_sourceRecordTokens]

/-- The compiled cycle occurrence blocks are exactly the header projection of
the canonical implication-cycle route records. -/
theorem directSourceFinalCycleOccurrenceData_eq_canonical
    (symbols : List encoding.Γ) :
    directSourceFinalCycleOccurrenceData decider symbols =
      HorizontalRoutedRouteHeaderOccurrence.output
        (HorizontalRoutedRouteTailRecord.batchedRecords
          (directFigureNineCycleRouteTailRecordTokens decider symbols)) := by
  unfold directSourceFinalCycleOccurrenceData
  rw [directFigureNineCycleRouteTailRecordTokensCompiled_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
