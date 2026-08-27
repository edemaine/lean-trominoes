/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPresentation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteMembership

/-! # Geometry of proof-free final gauged retained routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance finalGaugedRouteGeometryVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Every genuine route selected from the proof-free final gauged formula
contains a segment and is orthogonal. -/
theorem retainedOrderedFixedEightFinalGaugedComputedRoute_geometry_of_members
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
    2 ≤
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
          source clauseIndex literalIndex).length ∧
      OrthogonalPolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
          source clauseIndex literalIndex) := by
  have proofClauseMember :
      (gaugedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty] using
      clauseMember
  have routeMember :
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
          clauseIndex literalIndex ∈
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).edgeRoutes := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing] using
      PositionedPeriodicCNF.incidenceRoute_mem_edgeRoutes
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
        proofClauseMember literalMember
  constructor
  · rw [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty]
    exact
      PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.incidenceGraph
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isCompatible
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
        (PeriodicCNF.incidenceGraph_edgesAreLoopless
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty).erase)
        routeMember
  · rw [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty]
    exact
      (PeriodicGridDrawing.isOrthogonal_iff_routes
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceDrawing
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)).mp
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isOrthogonal
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
        _ routeMember

end PeriodicOrthocrossing
end LeanTrominoes
