import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation

/-!
# Endpoint isolation for final positioned fallbacks

The reusable ordinary and escaped fan-splice certificates are instantiated
with the final retained source route, terminal classification, and positioned
Figure 7 spoke.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- Every genuine ordinary fallback in the final positioned construction
has an isolated variable endpoint after unit subdivision. -/
theorem retainedFinalOrdinaryFallbackOccurrenceRoute_lastNotInDropLast
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
          formula clauseIndex literalIndex = none) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
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
  let sourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause)
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
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
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some sourcePoint := by
    simpa [route, rawRoute, sourcePoint] using
      finalCoordinatedScaledSourceRoute_head
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
  have retained : RetainedRayPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal := by
    have escapePositive :
        0 < retainedTerminalFanOuterSourceEscapeLength := by
      native_decide
    omega
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes,
      finalPoint, center, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex =
        retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    rw [
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember]
    unfold retainedAngularFanSplicedOwnFigure7Route
    rw [spokeEqual]
  rw [routeEqual]
  exact
    retainedAngularFanSplicedOwnFigure7Route_lastNotInDropLast
      route terminal slot sourcePoint finalPoint routeLength classified
      simple routeHead routeFinal routeOrthogonal retained
      radialLengthPositive

/-- Every genuine escaped fallback in the final positioned construction
has an isolated variable endpoint after unit subdivision. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_lastNotInDropLast
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
          formula clauseIndex literalIndex = none) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)) := by
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
  let sourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause)
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
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
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some sourcePoint := by
    simpa [route, rawRoute, sourcePoint] using
      finalCoordinatedScaledSourceRoute_head
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
  have retained : RetainedRayPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes,
      finalPoint, center, slot] using
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
    retainedAngularFanEscapedSplicedOwnFigure7Route_lastNotInDropLast
      route terminal slot sourcePoint finalPoint routeLength classified
      simple routeHead routeFinal routeOrthogonal retained escapeFits

end PeriodicOrthocrossing
end LeanTrominoes
