/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFigureNineCopiedRouteTailRecordFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverPhaseNormalizedSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompiledRecordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedPhaseNormalizedSemantics
import LeanTrominoes.RetainedAngularFanNormalizedClauseBatchedRecordSemantics

/-! # Semantics of the compiled five-family direct final records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyCompiledRecordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFiveFamilyCompiledRecordSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled crossover phase expands to its normalized semantic block. -/
theorem directSourceFinalCrossoverBatchedRecords_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalCrossoverBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols) 0
          (directSourceFinalCrossoverClauses decider symbols)) := by
  unfold directSourceFinalCrossoverBatchedRecords
  rw [directSourceFinalCrossoverRouteTailRecordTokens_eq_normalizedSemantic]

/-- The compiled routed suffix expands to its two normalized semantic blocks. -/
theorem directSourceFinalRoutedBatchedRecords_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
            (directSourceFormula decider symbols)
            (directSourceFinalRoutedClauseStart decider symbols)
            (directSourceFinalRoutedClauseClauses decider symbols) ++
          retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
            (directSourceFormula decider symbols)
            (directSourceFinalRoutedVariableStart decider symbols)
            (directSourceFinalRoutedVariableClauses decider symbols)) := by
  unfold directSourceFinalRoutedBatchedRecords
  rw [directSourceFinalRoutedRouteTailRecordTokens_eq_normalizedSemantic]

/-- Re-express the carrier result under the canonical direct-source equality
used by the complete five-family presentation. -/
private theorem directSourceFinalCarrierCompiledBatchedRecords_eq_canonical
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierCompiledBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (@retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          Variable directSourceVariableDecidableEq
          (directSourceFormula decider symbols)
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) := by
  let statement (equality : DecidableEq Variable) : Prop :=
    directSourceFinalCarrierCompiledBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (@retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          Variable equality
          (directSourceFormula decider symbols)
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols))
  let structuralEquality : DecidableEq Variable := fun a b =>
    @PeriodicOrthocrossing.drawingOrderedThreeOccurrenceVariableInstDecidableEq
      (ThreeCNFVariable Nat) directSourceFinalStructuralBaseDecidableEq a b
  have structural : statement structuralEquality :=
    directSourceFinalCarrierCompiledBatchedRecords_eq_semantic
      decider symbols
  have equalityIrrel := decidableEq_application_irrel statement
    structuralEquality
    directSourceVariableDecidableEq
  change statement directSourceVariableDecidableEq
  exact equalityIrrel ▸ structural

/-- Re-express the bend result under the canonical direct-source equality. -/
private theorem directSourceFinalBendCompiledBatchedRecords_eq_canonical
    (symbols : List encoding.Γ) :
    directSourceFinalBendCompiledBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (@retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          Variable directSourceVariableDecidableEq
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) := by
  let statement (equality : DecidableEq Variable) : Prop :=
    directSourceFinalBendCompiledBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (@retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          Variable equality
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols))
  let bendEquality : DecidableEq Variable :=
    directFinalBendCompiledBatchedRecordVariableDecidableEq
  have original : statement bendEquality :=
    directSourceFinalBendCompiledBatchedRecords_eq_semantic decider symbols
  have equalityIrrel := decidableEq_application_irrel statement
    bendEquality
    directSourceVariableDecidableEq
  change statement directSourceVariableDecidableEq
  exact equalityIrrel ▸ original

/-- The assembled physical stream is exactly the expanded copied-clause
prefix of the retained Figure 9 route-tail records. -/
theorem directSourceFinalFiveFamilyCompiledRecords_eq_copied
    (symbols : List encoding.Γ) :
    directSourceFinalFiveFamilyCompiledRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (directFigureNineCopiedRouteTailRecordTokens decider symbols) := by
  unfold directSourceFinalFiveFamilyCompiledRecords
    directSourceFinalCrossoverCarrierCompiledRecords
    directSourceFinalBendRoutedCompiledRecords
  rw [directSourceFinalCrossoverBatchedRecords_eq_semantic,
    directSourceFinalCarrierCompiledBatchedRecords_eq_canonical,
    directSourceFinalBendCompiledBatchedRecords_eq_canonical,
    directSourceFinalRoutedBatchedRecords_eq_semantic,
    directFigureNineCopiedRouteTailRecordTokens_eq_fiveFamilies]
  simp only [
    batchedRecords_retainedFinalNormalizedClauseSemantic_append,
    List.append_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
