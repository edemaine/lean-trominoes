/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseTaggedPermutationSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDirectionData

/-! # Exact raw source indices of final gauged Figure 9 routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

local instance finalGaugedExactSourceIndexVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Final clockwise ordering and the subsequent gauge select the exact raw
literal index prescribed by `reorderList` on the original index range, while
preserving the complete normalized direction word. -/
theorem
    exists_composedRawLiteral_finalGauged_directionWord_exactSourceIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {orderedClause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (orderedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ sourceClause sourceLiteral sourceLiteralIndex,
      (sourceClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx ∧
      sourceLiteralIndex =
        (PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
          (List.range sourceClause.literals.length)).getD literalIndex 0 ∧
      literal = sourceLiteral ∧
      unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex) =
        unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex sourceLiteralIndex) := by
  have orderedClauseMember :
      (orderedClause, clauseIndex) ∈
        (PositionedPeriodicCNF.orderClausesByRouteDirection
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)).clauses.zipIdx := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
      using clauseMember
  rcases
      PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        orderedClauseMember with
    ⟨sourceClause, sourceClauseMember, orderedClauseEq⟩
  have literalLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp literalMember
  rw [orderedClauseEq, PositionedPeriodicCNF.orderClauseByRouteDirection,
    List.getElem?_map, Option.map_eq_some_iff] at literalLookup
  rcases literalLookup with
    ⟨taggedLiteral, taggedLookup, taggedLiteralEq⟩
  have taggedOrder :=
    retainedOrderedFixedEight_clauseLiteralOrder_eq_reorderList_zipIdx
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember
  rw [taggedOrder] at taggedLookup
  have reorderedMember :
      taggedLiteral ∈
        PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
          sourceClause.literals.zipIdx :=
    List.mem_iff_getElem?.mpr ⟨literalIndex, taggedLookup⟩
  have sourceLiteralMember :
      taggedLiteral ∈ sourceClause.literals.zipIdx :=
    PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.mem_of_mem_reorderList
      reorderedMember
  have taggedLt : literalIndex <
      (PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
        sourceClause.literals.zipIdx).length :=
    (List.getElem?_eq_some_iff.mp taggedLookup).1
  have taggedAt := (List.getElem?_eq_some_iff.mp taggedLookup).2
  have sourceLiteralIndexEq :
      taggedLiteral.2 =
        (PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
          (List.range sourceClause.literals.length)).getD literalIndex 0 := by
    rw [←
      PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList_zipIdx_getD_snd
        sourceClause.literals taggedLiteral.1 literalIndex]
    rw [List.getD_eq_getElem _ _ taggedLt, taggedAt]
  have sourceClauseLookup :=
    (List.mk_mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have clockwiseDirections :
      unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex) =
        unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex taggedLiteral.2) := by
    unfold
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
      PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
    rw [sourceClauseLookup]
    rw [unitSubdivisionDirections_translatePolyline]
    unfold PositionedPeriodicCNF.orderRoutesByClauseDirection
    rw [sourceClauseLookup]
    simp only
    rw [taggedOrder, taggedLookup]
  have gaugedDirections :=
    PositionedPeriodicCNF.unitSubdivisionDirections_variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (literalIndex := literalIndex) clauseMember
  refine ⟨sourceClause, taggedLiteral.1, taggedLiteral.2,
    sourceClauseMember, sourceLiteralMember, sourceLiteralIndexEq,
    taggedLiteralEq.symm, ?_⟩
  exact gaugedDirections.trans clockwiseDirections

end PeriodicOrthocrossing
end LeanTrominoes
