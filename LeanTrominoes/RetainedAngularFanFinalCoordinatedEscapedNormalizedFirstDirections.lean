/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalEscapedNormalizedFirstDirections
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-! # Public normalized directions of escaped fallback routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- A genuine singleton failed-direct incidence exposes the first direction
of its scaled source edge at the public normalized route boundary. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_escapedFallback_firstDirection
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
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) := by
  unfold
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_fallbackOccurrenceRoute_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone]
  unfold retainedFinalFallbackOccurrenceRoute
  rw [if_pos singletonPrefix]
  exact
    retainedFinalEscapedFallbackOccurrenceRoute_normalized_firstDirection
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      choiceNone singletonPrefix

end PeriodicOrthocrossing
end LeanTrominoes
