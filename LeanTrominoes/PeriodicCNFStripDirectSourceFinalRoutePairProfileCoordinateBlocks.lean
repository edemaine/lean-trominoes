/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithExpectedFlatten
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixProfileCoordinateBlocks
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairProfileCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSourceIndexedPolarityOperationSemantics

/-! # Generated-clause indexing of direct Figure 9 profile coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalProfileCoordinateBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalProfileCoordinateBlocksVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem profileCoordinateBlocksDirectSourceIsLocal
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).IsLocal := by
  simpa only [directSourceFormula] using
    sourceFormula_isLocal
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem profileCoordinateBlocksDirectSourceWidthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  simpa only [directSourceFormula] using
    sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem profileCoordinateBlocksDirectSourceOccurrencesAtMostThree
    (symbols : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 (directSourceFormula decider symbols) := by
  unfold directSourceFormula
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_occurrencesAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols))

private theorem profileCoordinateBlocksDirectSourceClausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  simpa only [directSourceFormula] using
    sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- The actual final formula's per-clause polarity blocks are exactly the
polarity projections of the profile-qualified Figure 9 coordinate blocks. -/
theorem directSourceFinalPolarityDescriptorBlocks_eq_profileCoordinateBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalPolarityDescriptorBlocks decider symbols =
      ((FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          expectedHeaderTemplateProfileCoordinateBlocks).map
            (List.map fun coordinate => coordinate.coordinate.polarity) := by
  have gaugedValueEq :=
    PositionedPeriodicCNF.variableGauge_clauseLiteralValues
      (directSourceFinalClockwiseFormula decider symbols)
      (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        (directSourceFormula decider symbols))
  have finalValueEq :=
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_clauseLiteralValues_eq_descriptors
      (directSourceFormula decider symbols)
      (profileCoordinateBlocksDirectSourceIsLocal decider symbols)
      (profileCoordinateBlocksDirectSourceWidthAtMostThree decider symbols)
      (profileCoordinateBlocksDirectSourceOccurrencesAtMostThree
        decider symbols)
      (profileCoordinateBlocksDirectSourceClausesNonempty decider symbols)
  calc
    _ = ((directSourceFinalGaugedFormula decider symbols).clauses.map
          fun clause => clause.literals.map PeriodicLiteral.value).map
            ClauseProfilePolarityRouteOperation.indexedDescriptors := by
      simp only [directSourceFinalPolarityDescriptorBlocks,
        List.map_map, Function.comp_def]
    _ = ((directSourceFinalClockwiseFormula decider symbols).clauses.map
          fun clause => clause.literals.map PeriodicLiteral.value).map
            ClauseProfilePolarityRouteOperation.indexedDescriptors := by
      rw [directSourceFinalGaugedFormula, gaugedValueEq]
    _ = ((FormulaShapeRetainedFigureNineDirection.descriptors
          (directSourceFormula decider symbols)).flatMap
            FormulaShapeFigureNineFinalClauseOrdering.finalClauseLiteralValueBlock).map
                ClauseProfilePolarityRouteOperation.indexedDescriptors := by
      rw [directSourceFinalClockwiseFormula, finalValueEq]
    _ = _ := by
      exact
        (source_flatMap_expectedHeaderTemplateProfileCoordinateBlocks_map_polarity
          (FormulaShapeRetainedFigureNineDirection.descriptors
            (directSourceFormula decider symbols))).symm

/-- The direct broadcast parent-clause column is the ordinary `zipIdx`
column of the finite profile-coordinate blocks. -/
theorem directFigureNinePolarityRoutePairSourceClauseIndices_eq_profileCoordinateBlocks
    (symbols : List encoding.Γ) :
    directFigureNinePolarityRoutePairSourceClauseIndices decider symbols =
      (((FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          expectedHeaderTemplateProfileCoordinateBlocks).zipIdx.flatMap
            fun taggedBlock =>
              List.replicate taggedBlock.1.length taggedBlock.2) := by
  unfold directFigureNinePolarityRoutePairSourceClauseIndices
  rw [directSourceFinalPolarityDescriptorBlocks_eq_profileCoordinateBlocks]
  simp only [List.zipIdx_map, List.flatMap_map,
    List.length_map, Prod.map, id_eq]

/-- Attaching the direct parent-clause index to every header yields the
blockwise globally indexed profile-coordinate schedule. -/
theorem directFigureNinePolarityRoutePairs_zipWith_sourceProfileCoordinate
    (symbols : List encoding.Γ) :
    List.zipWith
        (fun sourceClauseIndex pair =>
          (sourceClauseIndex,
            headerTemplateProfileCoordinate pair.1))
        (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols)
        (directFigureNinePolarityRoutePairs decider symbols) =
      ((FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          expectedHeaderTemplateProfileCoordinateBlocks).zipIdx.flatMap
            fun taggedBlock =>
              taggedBlock.1.map fun coordinate =>
                (taggedBlock.2, coordinate) := by
  rw [← List.zipWith_map_right]
  rw [directFigureNinePolarityRoutePairs_map_headerTemplateProfileCoordinate]
  rw [←
    source_flatMap_expectedHeaderTemplateProfileCoordinateBlocks_flatten]
  rw [
    directFigureNinePolarityRoutePairSourceClauseIndices_eq_profileCoordinateBlocks]
  exact
    List.zipWith_zipIdxReplicate_flatten_eq_zipIdx_flatMap_zero
      (fun sourceClauseIndex coordinate =>
        (sourceClauseIndex, coordinate)) _

end LeanTrominoes.PeriodicCNFStripReduction

end
