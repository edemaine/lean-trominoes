/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmFamilyBridge
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedVariableDescriptorPairScanSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedVariablePairScan
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariablePairSemanticBridge

/-! # Correctness of direct retained routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedVariableSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private noncomputable def
    directRetainedRoutedVariableSemanticsStructuralVariableDecidableEq :
    DecidableEq Variable :=
  inferInstance

local instance directRetainedRoutedVariableSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directRetainedClauseFamilyDataVariableDecidableEq

/-- The descriptor-pair scan emits exactly the retained routed-variable
descriptor family of the direct geometric source. -/
theorem
    directRetainedPlanarMetadataRoutedVariableClauseDescriptors_eq_compiled
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataRoutedVariableClauseDescriptors
        decider symbols =
      directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
        decider symbols := by
  let source := PeriodicThreeCNF.formula
    (PolySpaceCompiler.formulaOfSymbols decider symbols)
  rw [directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors_eq_pairScan]
  trans routedVariablePairDescriptorScan
      (PeriodicThreeSATThree.splitRouteDescriptors source)
  · unfold directRetainedPlanarMetadataRoutedVariableClauseDescriptors
    apply Eq.trans
    · apply
        routedVariableMetadataClauseDescriptors_eq_numericOccurrenceSiteArmStream
      · exact PeriodicCNF.incidenceGraph_isWellFormed _
      · unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
    · rw [directSourceFormula_eq_threeSATThree]
      have familyInstanceEq :
          directRetainedClauseFamilyDataVariableDecidableEq =
            directRetainedRoutedVariableSemanticsStructuralVariableDecidableEq :=
        Subsingleton.elim _ _
      have localInstanceEq :
          directRetainedRoutedVariableSemanticsVariableDecidableEq =
            directRetainedRoutedVariableSemanticsStructuralVariableDecidableEq :=
        Subsingleton.elim _ _
      rw [familyInstanceEq, localInstanceEq]
      apply
        PeriodicThreeSATThree.routedVariableNumericOccurrenceSiteArmStream_formula_eq_pairScan
      exact directThreeCNFSource_occurrenceIncidences_positiveOffsets
        decider symbols
  · have localInstanceEq :
        directRetainedRoutedVariableSemanticsVariableDecidableEq =
          directSourceRoutedVariablePairScanVariableDecidableEq :=
      Subsingleton.elim _ _
    have compiledInstanceEq :
        directRetainedRoutedVariablePairScanVariableDecidableEq =
          directSourceRoutedVariablePairScanVariableDecidableEq :=
      Subsingleton.elim _ _
    rw [localInstanceEq, compiledInstanceEq]
    exact
      (directSource_routedVariablePairDescriptorScan_eq_split
        decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
