/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrderingDirections
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDirectionData

/-! # Directions through the final fixed-eight variable gauge -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

/-- The final fixed-eight gauge changes route coordinates but not directions. -/
theorem
    retainedOrderedFixedEightFinalGauged_directionWord_of_clause_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
          source).clauses.zipIdx) :
    unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
          source clauseIndex literalIndex) =
      unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutesComputed
          source clauseIndex literalIndex) := by
  unfold
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
  exact
    PositionedPeriodicCNF.unitSubdivisionDirections_variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutesComputed
        source)
      clauseMember

/-- Final clockwise ordering and the subsequent gauge reduce to one original
literal index of the composed raw formula, with an unchanged normalized
direction word. -/
theorem
    exists_composedRawLiteral_finalGauged_directionWord
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
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
    ∃ sourceClause sourceLiteral sourceLiteralIndex,
      (sourceClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx ∧
      literal = sourceLiteral ∧
      unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
            source clauseIndex literalIndex) =
        unitSubdivisionDirections
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
            source clauseIndex sourceLiteralIndex) := by
  have orderedClauseMember :
      (orderedClause, clauseIndex) ∈
        (PositionedPeriodicCNF.orderClausesByRouteDirection
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
            source)).clauses.zipIdx := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed]
      using clauseMember
  rcases
      PositionedPeriodicCNF.exists_sourceLiteral_directionWord_of_orderedLiteral_mem
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutesComputed
          source)
        orderedClauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember, literalEq,
      clockwiseDirections⟩
  refine ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
    sourceClauseMember, sourceLiteralMember, literalEq, ?_⟩
  rw [retainedOrderedFixedEightFinalGauged_directionWord_of_clause_mem
    source clauseMember]
  exact clockwiseDirections

end PeriodicOrthocrossing
end LeanTrominoes
