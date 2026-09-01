/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledOccurrenceData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockSemantics
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Canonical semantics of direct copied-clause occurrence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedOccurrenceBlockSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCopiedOccurrenceBlockSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The independently compiled copied-clause occurrence blocks are exactly
the header projection of the canonical copied Figure 9 route records. -/
theorem directSourceFinalCopiedOccurrenceData_eq_canonical
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedOccurrenceData decider symbols =
      HorizontalRoutedRouteHeaderOccurrence.output
        (HorizontalRoutedRouteTailRecord.batchedRecords
          (directFigureNineCopiedRouteTailRecordTokens decider symbols)) := by
  let source := directSourceFormula decider symbols
  calc
    directSourceFinalCopiedOccurrenceData decider symbols =
        HorizontalRoutedRouteHeaderOccurrenceBlock.output
          (@FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
            Variable directSourceVariableDecidableEq source) := by
      change HorizontalRoutedRouteHeaderOccurrenceBlock.output
          (@FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
            Variable (Classical.decEq Variable) source) = _
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          HorizontalRoutedRouteHeaderOccurrenceBlock.output
            (@FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
              Variable equality source))
        (Classical.decEq Variable) directSourceVariableDecidableEq
    _ = HorizontalRoutedRouteHeaderOccurrenceBlock.output
          (@FormulaShapeRetainedFigureNineDirection.routedCopiedClauseDescriptors
            Variable directSourceVariableDecidableEq source) := by
      apply congrArg HorizontalRoutedRouteHeaderOccurrenceBlock.output
      exact
        (FormulaShapeRetainedFigureNineDirection.routedCopiedClauseDescriptors_eq_copiedClauseDescriptors
            source
            (sourceFormula_isLocal
              (PolySpaceCompiler.formulaOfSymbols decider symbols))
            (sourceFormula_widthAtMostThree
              (PolySpaceCompiler.formulaOfSymbols decider symbols))
            (sourceFormula_occurrencesAtMostThree
              (PolySpaceCompiler.formulaOfSymbols decider symbols))
            (sourceFormula_clausesNonempty
              (PolySpaceCompiler.formulaOfSymbols decider symbols))).symm
    _ = HorizontalRoutedRouteHeaderOccurrence.output
          (HorizontalRoutedRouteTailRecord.batchedRecords
            (directFigureNineCopiedRouteTailRecordTokens decider symbols)) := by
      unfold directFigureNineCopiedRouteTailRecordTokens
        FormulaShapeRetainedFigureNineSourceTailRecord.copiedRecordTokens
      rw [HorizontalRoutedRouteHeaderOccurrenceBlock.occurrenceOutput_batchedRecords_sourceRecordTokens]

/-- The complete compiled occurrence stream splits at the same exact copied
prefix, followed by the independently compiled implication-cycle suffix. -/
theorem directSourceFinalCompiledOccurrenceData_eq_copied_cycle
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledOccurrenceData decider symbols =
      directSourceFinalCopiedOccurrenceData decider symbols ++
        directSourceFinalCycleOccurrenceData decider symbols := by
  unfold directSourceFinalCompiledOccurrenceData
    directSourceFinalCompiledRouteTailRecords
    directSourceFinalCycleCompiledBatchedRecords
  rw [HorizontalRoutedRouteHeaderOccurrence.output_append,
    directSourceFinalFiveFamilyCompiledRecords_eq_copied,
    ← directSourceFinalCopiedOccurrenceData_eq_canonical,
    ← directSourceFinalCycleOccurrenceData_eq_canonical]

end LeanTrominoes.PeriodicCNFStripReduction

end
