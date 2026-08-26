/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEscapedOwnFigure7NormalizedFirstDirections
import LeanTrominoes.RetainedAngularFanFinalFallbackEndpointIsolation

/-! # Normalized first directions of final escaped fallback routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- A genuine singleton failed-direct occurrence retains the first direction
of its scaled source edge after the complete escaped fallback is normalized. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_normalized_firstDirection
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
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFinalEscapedFallbackOccurrenceRoute
            formula
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)) =
      AxisDirection.polylineFirstDirection
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) := by
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
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
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
  have routeLength : 2 ≤ route.length := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have classified :
      retainedTerminalDirectionClassify (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal, rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledSingletonPrefix : route.dropLast.length = 1 := by
    simpa [route, rawRoute, scalePolyline] using singletonPrefix
  have rawTerminalPositive : 0 < rawTerminal.2 := by
    simpa [rawTerminal, rawRoute] using
      finalCoordinatedSourceRoute_terminal_length_positive
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have terminalLengthLarge : 2 ≤ terminal.2 := by
    change
      2 ≤
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal).2
    rw [scaleRetainedTerminalData_length,
      retainedAngularFanSourceClearanceFactor_eq]
    omega
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes,
      finalPoint, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
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
  rw [routeEqual]
  exact
    retainedAngularFanEscapedSplicedOwnFigure7Route_normalized_firstDirection
      route terminal slot finalPoint routeLength classified routeFinal
      routeOrthogonal escapeFits scaledSingletonPrefix terminalLengthLarge

end PeriodicOrthocrossing
end LeanTrominoes
