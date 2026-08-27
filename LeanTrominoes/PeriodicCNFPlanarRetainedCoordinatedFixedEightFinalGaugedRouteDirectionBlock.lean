/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineCompleteRouteDirectionBlock
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRouteDirections
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership

/-! # Compact direction blocks after final clockwise ordering and gauging -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

local instance finalGaugedRouteDirectionBlockVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Final clockwise reindexing and the final variable gauge preserve the
compact direction-block classification of every genuine Figure 9 route. -/
theorem
    retainedOrderedFixedEightFinalGaugedRoute_directionBlock_of_members
    {Variable : Type} [DecidableEq Variable]
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
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
          source).clauses.zipIdx)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ orderedClause.literals.zipIdx) :
    ∃ block : RetainedFigureNineRouteDirectionBlock,
      unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
            source clauseIndex literalIndex) =
        block.directions := by
  rcases
      exists_composedRawLiteral_finalGauged_directionWord
        source clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember, _literalEq,
      gaugedDirections⟩
  rcases
      retainedOrderedFixedEightFigureNineRoute_directionBlock_of_members
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember with
    ⟨block, blockDirections⟩
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex sourceLiteralIndex] at gaugedDirections
  refine ⟨block, gaugedDirections.trans ?_⟩
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes,
    PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes] using
    blockDirections

/-- The same classification can be selected directly from the proof-free
gauged formula consumed by polarity normalization. -/
theorem
    retainedOrderedFixedEightFinalGaugedComputedRoute_directionBlock_of_members
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {gaugedClause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (gaugedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
          source).clauses.zipIdx)
    {gaugedLiteral : PeriodicLiteral
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (gaugedLiteral, literalIndex) ∈ gaugedClause.literals.zipIdx) :
    ∃ block : RetainedFigureNineRouteDirectionBlock,
      unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
            source clauseIndex literalIndex) =
        block.directions := by
  have gaugedMember :
      (gaugedClause, clauseIndex) ∈
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
          source).variableGauge
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
              source)).clauses.zipIdx := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed]
      using clauseMember
  rcases
      PositionedPeriodicCNF.exists_sourceClause_of_variableGaugeClause_mem
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source)
        gaugedMember with
    ⟨sourceClause, sourceClauseMember, gaugedClauseEq⟩
  have gaugedLiteralLookup :
      (sourceClause.literals.variableGauge
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source))[literalIndex]? = some gaugedLiteral := by
    rw [gaugedClauseEq] at literalMember
    exact (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [PeriodicClause.variableGauge, List.getElem?_map] at gaugedLiteralLookup
  rcases Option.map_eq_some_iff.mp gaugedLiteralLookup with
    ⟨sourceLiteral, sourceLiteralLookup, _gaugedLiteralEq⟩
  have sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈ sourceClause.literals.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
  exact
    retainedOrderedFixedEightFinalGaugedRoute_directionBlock_of_members
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
