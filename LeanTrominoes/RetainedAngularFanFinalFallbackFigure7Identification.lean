/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOrdinaryFigure7Identification
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition

/-! # Uniform Figure 7 model for final fallback routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- The public singleton-prefix fallback is exactly the uniform ordinary-or-
escaped Figure 7 splice selected by the same policy. -/
theorem retainedFinalFallbackOccurrenceRoute_eq_kind_splicedOwnFigure7Route
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
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    retainedFinalFallbackOccurrenceRoute
        formula clause literal clauseIndex literalIndex =
      (if rawRoute.dropLast.length = 1 then
          RetainedFallbackFanKind.escaped
        else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
          route terminal slot := by
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
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
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
  have escapedEqual :
      retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex =
        retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    change
      joinAtEndpoint
          (retainedAngularFanEscapedSplicedBoundaryRoute
            route terminal slot)
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix placement
              (angularOccurrenceOrder source.erase routes)
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal clauseIndex literalIndex)) =
        retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint
    unfold retainedAngularFanEscapedSplicedOwnFigure7Route
    rw [spokeEqual]
  have ordinaryEqual :
      retainedFinalOrdinaryFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex =
        retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    simpa [rawRoute, route, rawTerminal, terminal,
      finalPoint, slot] using
      retainedFinalOrdinaryFallbackOccurrenceRoute_eq_splicedOwnFigure7Route
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [retainedFinalFallbackOccurrenceRoute,
      if_pos singletonPrefix, escapedEqual]
    change
      retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint =
        (if rawRoute.dropLast.length = 1 then
            RetainedFallbackFanKind.escaped
          else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
            route terminal slot
    rw [if_pos singletonPrefix]
    unfold RetainedFallbackFanKind.splicedOwnFigure7Route
    rw [routeLastD]
  · rw [retainedFinalFallbackOccurrenceRoute,
      if_neg singletonPrefix, ordinaryEqual]
    change
      retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint =
        (if rawRoute.dropLast.length = 1 then
            RetainedFallbackFanKind.escaped
          else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
            route terminal slot
    rw [if_neg singletonPrefix]
    unfold RetainedFallbackFanKind.splicedOwnFigure7Route
    rw [routeLastD]

end PeriodicOrthocrossing
end LeanTrominoes
