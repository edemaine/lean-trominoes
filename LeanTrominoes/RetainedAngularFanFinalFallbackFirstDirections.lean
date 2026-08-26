/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackFirstDirections
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-! # Clause-side directions of final ordinary fallback routes

The ordinary failed-direct branch retains at least two source-prefix points.
Consequently its clause-side direction is the first direction of the
source-clearance-scaled source route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- A genuine non-singleton failed-direct incidence exposes the first
direction of its source-clearance-scaled source route before loop erasure. -/
theorem
    retainedFinalOrdinaryFallbackOccurrenceRoute_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (prefixLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length ≠ 1) :
    AxisDirection.polylineFirstDirection
        (retainedFinalOrdinaryFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) := by
  have rawRouteLength :
      2 ≤
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).length :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawRouteLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).length ≠ 2 := by
    intro lengthEq
    apply prefixLengthNe
    rw [List.length_dropLast, lengthEq]
  have routeLength :
      3 ≤
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)).length := by
    simp only [scalePolyline, List.length_map]
    omega
  unfold retainedFinalOrdinaryFallbackOccurrenceRoute
  apply
    retainedAngularFanSplicedBoundaryRoute_joinAtEndpoint_firstDirection
  · exact routeLength
  · exact
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · exact
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  · exact
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
