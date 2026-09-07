/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLocalRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedExactSourceIndex

/-! # Final gauged route indices of Figure 9 source occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open Gadget

local instance occurrenceFinalGaugedVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The occurrence's final literal slot selects its exact raw local-query
index. Clockwise reordering and the final gauge preserve the entire route
direction word at these two corresponding indices. -/
theorem OccurrenceWitness.finalGaugedDirectionWord
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty
          occurrence.generatedClauseIndex occurrence.header.polarity.indexed.sourceLiteralIndex) =
      unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty
          occurrence.generatedClauseIndex
          (headerTemplateCoordinate occurrence.header).literalIndex) := by
  let routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
  let orderedClause := PositionedPeriodicCNF.orderClauseByRouteDirection routes
    occurrence.generatedClauseIndex witness.metadata.clause
  have orderedMember :
      (orderedClause, occurrence.generatedClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx :=
    PositionedPeriodicCNF.orderClauseByRouteDirection_mem routes witness.rawClauseMember
  obtain ⟨finalLt, rawIndexEq, _⟩ := witness.rawLiteralCoordinates sourceWidth sourceNonempty
  have literalLt : occurrence.header.polarity.indexed.sourceLiteralIndex <
      orderedClause.literals.length := by
    simpa only [orderedClause, PositionedPeriodicCNF.orderClauseByRouteDirection_length,
      headerTemplateCoordinate]
      using finalLt
  have literalMember :
      (orderedClause.literals[occurrence.header.polarity.indexed.sourceLiteralIndex],
        occurrence.header.polarity.indexed.sourceLiteralIndex) ∈
          orderedClause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem literalLt)
  obtain ⟨rawClause, _, rawIndex, rawMember, _, indexEq, _, directionsEq⟩ :=
    exists_composedRawLiteral_finalGauged_directionWord_exactSourceIndex
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
      orderedMember literalMember
  have rawClauseEq : rawClause = witness.metadata.clause :=
    Option.some.inj ((List.mk_mem_zipIdx_iff_getElem?.mp rawMember).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp witness.rawClauseMember))
  subst rawClause
  have rawIndexEq' : rawIndex = (headerTemplateCoordinate occurrence.header).literalIndex :=
    indexEq.trans rawIndexEq.symm
  rwa [rawIndexEq'] at directionsEq

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
