/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineIndexedProfileCoordinateBlocks
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairProfileCoordinateBlocks

/-! # Direct Figure 9 metadata profile-coordinate semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalMetadataProfileCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalMetadataProfileCoordinateVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceWidthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  simpa only [directSourceFormula] using
    sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceClausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  simpa only [directSourceFormula] using
    sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- The direct globally indexed coordinate stream is the flattening of the
parent-indexed finite blocks, not merely of their coordinate projection. -/
theorem directFigureNinePolarityRoutePairs_zipWith_indexedProfileCoordinate
    (symbols : List encoding.Γ) :
    List.zipWith
        (fun sourceClauseIndex pair =>
          (sourceClauseIndex,
            headerTemplateProfileCoordinate pair.1))
        (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols)
        (directFigureNinePolarityRoutePairs decider symbols) =
      (((PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          expectedIndexedProfileCoordinateBlocks).zipIdx.flatMap
            fun taggedBlock =>
              taggedBlock.1.coordinates.map fun coordinate =>
                (taggedBlock.2, coordinate)) := by
  rw [directFigureNinePolarityRoutePairs_zipWith_sourceProfileCoordinate]
  rw [← source_flatMap_expectedIndexedProfileCoordinateBlocks_map_coordinates]
  simp only [List.zipIdx_map, List.flatMap_map, Prod.map, id_eq]

/-- The parent coordinates of the direct indexed blocks are exactly those
of the concrete retained Figure 9 metadata list. -/
theorem directSourceIndexedProfileCoordinateBlocks_map_parent_eq_metadata
    (symbols : List encoding.Γ) :
    (((PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
      (directSourceFormula decider symbols)).flatMap
        expectedIndexedProfileCoordinateBlocks).map
          IndexedProfileCoordinateBlock.parent) =
      (formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula
          (directSourceFormula decider symbols))).map
            ClauseMetadata.parentProfileCoordinate := by
  exact
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.indexedProfileCoordinateBlocks_map_parent_eq_metadata
      (directSourceFormula decider symbols)
      (directSourceWidthAtMostThree decider symbols)
      (directSourceClausesNonempty decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
