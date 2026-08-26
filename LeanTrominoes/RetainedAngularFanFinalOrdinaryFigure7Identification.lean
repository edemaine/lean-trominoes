/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels

/-! # Identifying final ordinary fallbacks with their Figure 7 model -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 500000

/-- At a genuine final occurrence, the explicit ordinary fallback is exactly
the generic source-boundary splice completed by its matching Figure 7 spoke. -/
theorem
    retainedFinalOrdinaryFallbackOccurrenceRoute_eq_splicedOwnFigure7Route
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let route :=
      scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
    let rawTerminal :=
      classifiedRetainedTerminalData (routeTerminalVector rawRoute)
    let terminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal
    let finalPoint :=
      Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    retainedFinalOrdinaryFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex =
      retainedAngularFanSplicedOwnFigure7Route
        route terminal slot finalPoint := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes, finalPoint, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  change
    joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          route terminal slot)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)) =
      retainedAngularFanSplicedOwnFigure7Route
        route terminal slot finalPoint
  unfold retainedAngularFanSplicedOwnFigure7Route
  rw [spokeEqual]

end PeriodicOrthocrossing
end LeanTrominoes
