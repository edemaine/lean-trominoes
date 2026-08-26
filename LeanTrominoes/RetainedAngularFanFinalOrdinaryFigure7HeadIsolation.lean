/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOrdinaryFallbackHeadSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteModels
import LeanTrominoes.RetainedAngularFanOrdinaryFigure7HeadIsolation

/-! # Final ordinary-fallback source-head isolation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 500000

/-- A genuine non-singleton failed-direct occurrence keeps its source head
isolated after unit subdivision of the explicit final ordinary route. -/
theorem retainedFinalOrdinaryFallbackOccurrenceRoute_headNotInTail
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
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (retainedFinalOrdinaryFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex)) := by
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
  let rawSourcePoint :=
    PositionedPeriodicCNF.canonicalClausePosition
      (finalCoordinatedPlacement formula) clause
  let routeSourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor rawSourcePoint
  let rawFinalPoint :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula) clause literal
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor rawFinalPoint
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have rawLength : 2 ≤ rawRoute.length :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawLengthNe : rawRoute.length ≠ 2 := by
    intro lengthEq
    apply prefixLengthNe
    simp [rawRoute, List.length_dropLast, lengthEq]
  have routeLength : 3 ≤ route.length := by
    simpa [route, scalePolyline] using
      (show 3 ≤ rawRoute.length by omega)
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) = some terminal := by
    simpa [route, rawRoute, terminal, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some routeSourcePoint := by
    simpa [route, rawRoute, routeSourcePoint, rawSourcePoint] using
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint, rawFinalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have absent :=
    retainedFinalOrdinaryFallback_sourceHead_not_mem_outer_and_spoke
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      choiceNone prefixLengthNe
  dsimp only at absent
  have headNotInOuter :
      Cell.scale retainedTerminalFanTotalRefinement routeSourcePoint ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot) := by
    rw [routeLastD]
    simpa [routeSourcePoint, rawSourcePoint, finalPoint,
      rawFinalPoint, terminal, rawTerminal, rawRoute, slot] using absent.1
  have headNotInSpoke :
      Cell.scale retainedTerminalFanTotalRefinement routeSourcePoint ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanFigure7SpokeRouteAt
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            slot) := by
    rw [routeLastD]
    simpa [routeSourcePoint, rawSourcePoint, finalPoint,
      rawFinalPoint, rawRoute, slot] using absent.2
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
      finalPoint, rawFinalPoint, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
      retainedFinalOrdinaryFallbackOccurrenceRoute
          formula clause literal clauseIndex literalIndex =
        retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint := by
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
  have fresh :=
    retainedAngularFanSplicedOwnFigure7Route_headNotInTail
      route terminal slot routeSourcePoint routeLength classified
      simple routeHead routeOrthogonal headNotInOuter headNotInSpoke
  rw [routeLastD] at fresh
  rw [routeEqual]
  exact fresh

end PeriodicOrthocrossing
end LeanTrominoes
