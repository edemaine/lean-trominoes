/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEscapedFirstDirections
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation

/-! # Clause-side directions of final escaped fallback routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- A genuine singleton failed-direct occurrence exposes the first direction
of its source-clearance-scaled source route before loop erasure. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_firstDirection
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
    (singletonPrefix :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length = 1) :
    AxisDirection.polylineFirstDirection
        (retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) := by
  have routeLength :
      2 ≤
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)).length :=
    finalCoordinatedScaledSourceRoute_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have classified :=
    finalCoordinatedScaledSourceRoute_classified
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have routeOrthogonal :=
    finalCoordinatedScaledFallbackSourceRoute_orthogonal
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone
  have escapeFits :=
    finalCoordinatedScaledSourceRoute_escapeFits
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have scaledSingletonPrefix :
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)).dropLast.length = 1 := by
    simpa [scalePolyline] using singletonPrefix
  unfold retainedFinalEscapedFallbackOccurrenceRoute
  apply
    retainedAngularFanEscapedSplicedBoundaryRoute_joinAtEndpoint_firstDirection
  · exact routeLength
  · exact classified
  · exact routeOrthogonal
  · exact escapeFits
  · exact scaledSingletonPrefix

end PeriodicOrthocrossing
end LeanTrominoes
