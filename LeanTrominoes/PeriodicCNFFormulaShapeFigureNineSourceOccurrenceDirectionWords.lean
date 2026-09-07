/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedRoutes
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderExactOperationSemantics

/-! # Complete source direction words of Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open PeriodicOrthocrossing
open Gadget
open PeriodicCNFStripReduction

local instance occurrenceDirectionWordsVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- A complete occurrence's header and dynamic tail denote the exact final
gauged source route at its attached clause and literal indices. -/
theorem OccurrenceWitness.sourceDirectionWord
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (HorizontalRoutedRouteHeader.sourceBlock occurrence.pair.1 occurrence.pair.2).directions =
      unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty
          occurrence.generatedClauseIndex occurrence.header.polarity.indexed.sourceLiteralIndex) := by
  rw [witness.finalGaugedDirectionWord sourceLocal sourceWidth sourceOccurrences sourceNonempty]
  change (HorizontalRoutedRouteHeader.sourceBlock occurrence.header occurrence.pair.2).directions = _
  cases prefixEq : occurrence.header.figurePrefix with
  | «local» query =>
    simp only [HorizontalRoutedRouteHeader.sourceBlock, prefixEq,
      RetainedFigureNineRouteDirectionBlock.directions]
    exact (witness.auxiliaryDirectionWord
      sourceLocal sourceWidth sourceOccurrences sourceNonempty query prefixEq).symm
  | inherited slot query =>
    simp only [HorizontalRoutedRouteHeader.sourceBlock, prefixEq,
      RetainedFigureNineRouteDirectionBlock.directions]
    exact (witness.inheritedDirectionWord
      sourceLocal sourceWidth sourceOccurrences sourceNonempty slot query prefixEq).symm

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
