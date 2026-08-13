/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceOwnCycleSeparation
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Complete fallback occurrences avoid their own implication cycle

The source-splice routes stop at the refined Figure 7 boundary.  This module
adds the matching factor-eight spoke.  The spoke continuously avoids every
inner implication route, and every permitted listed contact occurs at the
spoke's final ring vertex.  The tail-contact join theorem therefore combines
strict source-splice separation with the legal terminal contact.

Both ordinary and delayed-lane escaped fallback routes are covered.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The factor-eight Figure 7 spoke centered at a retained variable
position. -/
def retainedTerminalFanFigure7SpokeRouteAt
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    List Cell :=
  translatePolyline center
    (translatePolyline
      (Cell.sub (0, 0)
        (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
      (scalePolyline retainedTerminalFanRoutingRefinement
        (spokeRoute (angularPortOfIndex slot.val))))

/-- A centered Figure 7 spoke starts at its matching refined fan-boundary
site. -/
@[simp]
theorem retainedTerminalFanFigure7SpokeRouteAt_head?
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanFigure7SpokeRouteAt
      center slot).head? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  unfold retainedTerminalFanFigure7SpokeRouteAt
    translatePolyline scalePolyline
  simp only [List.head?_map, spokeRoute_head?, Option.map_some]
  apply congrArg some
  rcases center with ⟨centerX, centerY⟩
  rcases pointEq :
      spokeClausePosition (angularPortOfIndex slot.val) with
    ⟨pointX, pointY⟩
  simp [pointEq, angularFanBoundaryOffset,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- The centered factor-eight spoke ordinarily avoids every route of the
centered inner implication cycle. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_avoids_innerCycleRouteAt
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesAvoidEachOther
      (retainedTerminalFanFigure7SpokeRouteAt center slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  let localOffset :=
    Cell.sub (0, 0)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12))
  have scaledAvoid :=
    (spokeRoute_avoids_cycleRoute
      (angularPortOfIndex slot.val)
      vertex literalIndex.val).scalePolyline
        (show
          (0 : Int) < retainedTerminalFanRoutingRefinement by
          simp [retainedTerminalFanRoutingRefinement])
  have localAvoid :=
    routesAvoidEachOther_translate scaledAvoid localOffset
  have positionedAvoid :=
    routesAvoidEachOther_translate localAvoid center
  simpa [retainedTerminalFanFigure7SpokeRouteAt,
    retainedTerminalFanInnerCycleRouteAt,
    retainedTerminalFanInnerCycleRoute,
    translatePolyline, List.map_map, localOffset]
    using positionedAvoid

/-- Every listed spoke/cycle contact remains at the spoke's final ring
vertex after factor-eight scaling and positioning. -/
theorem
    retainedTerminalFanFigure7SpokeRouteAt_meets_innerCycleRouteAt_only_at_tail
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesMeetOnlyAtFirstTail
      (retainedTerminalFanFigure7SpokeRouteAt center slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  let localOffset :=
    Cell.sub (0, 0)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12))
  have scaledContacts :=
    (spokeRoute_meets_cycleRoute_only_at_tail
      (angularPortOfIndex slot.val)
      vertex literalIndex.val).scalePolyline
        (show
          (0 : Int) < retainedTerminalFanRoutingRefinement by
          simp [retainedTerminalFanRoutingRefinement])
  have localContacts :=
    scaledContacts.translate localOffset
  have positionedContacts :=
    localContacts.translate center
  simpa [retainedTerminalFanFigure7SpokeRouteAt,
    retainedTerminalFanInnerCycleRouteAt,
    retainedTerminalFanInnerCycleRoute,
    translatePolyline, List.map_map, localOffset]
    using positionedContacts

/-- One ordinary copied-source splice completed by its matching Figure 7
spoke. -/
def retainedAngularFanSplicedOwnFigure7Route
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell) :
    List Cell :=
  joinAtEndpoint
    (retainedAngularFanSplicedBoundaryRoute
      route terminal slot)
    (retainedTerminalFanFigure7SpokeRouteAt
      (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
      slot)

/-- A complete ordinary fallback occurrence avoids every implication route
in its own inner cycle, allowing only its final ring-vertex contact. -/
theorem
    retainedAngularFanSplicedOwnFigure7Route_avoids_innerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (source finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeHead : route.head? = some source)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (retained : RetainedRayPolyline route)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesAvoidEachOther
      (retainedAngularFanSplicedOwnFigure7Route
        route terminal slot finalPoint)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  let boundaryPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      route terminal slot
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther
        boundaryPrefix
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) := by
    simpa [boundaryPrefix, center] using
      retainedAngularFanSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
        route terminal slot finalPoint vertex literalIndex
        routeLength classified simple routeFinal routeOrthogonal
        radialLengthPositive
  have spokeAvoid :
      RoutesAvoidEachOther
        spoke
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) :=
    retainedTerminalFanFigure7SpokeRouteAt_avoids_innerCycleRouteAt
      center slot vertex literalIndex
  have spokeContacts :
      RoutesMeetOnlyAtFirstTail
        spoke
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) :=
    retainedTerminalFanFigure7SpokeRouteAt_meets_innerCycleRouteAt_only_at_tail
      center slot vertex literalIndex
  have boundaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      route terminal slot routeLength classified retained routeHead
  have routeLastD :
      route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have boundaryLast :
      boundaryPrefix.getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
    have boundaryLast' := boundaryValid.2.1
    change
      (retainedAngularFanSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add
              (Cell.scale retainedTerminalFanTotalRefinement
                (route.getLastD (0, 0)))
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val)))
      at boundaryLast'
    rw [routeLastD] at boundaryLast'
    exact boundaryLast'
  have spokeHead :
      spoke.head? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
    exact retainedTerminalFanFigure7SpokeRouteAt_head?
      center slot
  exact
    RoutesAvoidEachOther.join_left_of_tail_contact
      prefixAvoid spokeAvoid spokeContacts
      boundaryLast spokeHead

/-- One escaped copied-source splice completed by its matching Figure 7
spoke. -/
def retainedAngularFanEscapedSplicedOwnFigure7Route
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell) :
    List Cell :=
  joinAtEndpoint
    (retainedAngularFanEscapedSplicedBoundaryRoute
      route terminal slot)
    (retainedTerminalFanFigure7SpokeRouteAt
      (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
      slot)

/-- A complete escaped fallback occurrence avoids every implication route
in its own inner cycle, allowing only its final ring-vertex contact. -/
theorem
    retainedAngularFanEscapedSplicedOwnFigure7Route_avoids_innerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (source finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeHead : route.head? = some source)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (retained : RetainedRayPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesAvoidEachOther
      (retainedAngularFanEscapedSplicedOwnFigure7Route
        route terminal slot finalPoint)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  let boundaryPrefix :=
    retainedAngularFanEscapedSplicedBoundaryRoute
      route terminal slot
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther
        boundaryPrefix
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) := by
    simpa [boundaryPrefix, center] using
      retainedAngularFanEscapedSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
        route terminal slot finalPoint vertex literalIndex
        routeLength classified simple routeFinal routeOrthogonal
        escapeFits
  have spokeAvoid :
      RoutesAvoidEachOther
        spoke
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) :=
    retainedTerminalFanFigure7SpokeRouteAt_avoids_innerCycleRouteAt
      center slot vertex literalIndex
  have spokeContacts :
      RoutesMeetOnlyAtFirstTail
        spoke
        (retainedTerminalFanInnerCycleRouteAt
          center vertex literalIndex) :=
    retainedTerminalFanFigure7SpokeRouteAt_meets_innerCycleRouteAt_only_at_tail
      center slot vertex literalIndex
  have boundaryValid :=
    retainedAngularFanEscapedSplicedBoundaryRoute_valid
      route terminal slot routeLength classified retained routeHead
      escapeFits
  have routeLastD :
      route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have boundaryLast :
      boundaryPrefix.getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
    have boundaryLast' := boundaryValid.2.1
    change
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add
              (Cell.scale retainedTerminalFanTotalRefinement
                (route.getLastD (0, 0)))
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val)))
      at boundaryLast'
    rw [routeLastD] at boundaryLast'
    exact boundaryLast'
  have spokeHead :
      spoke.head? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
    exact retainedTerminalFanFigure7SpokeRouteAt_head?
      center slot
  exact
    RoutesAvoidEachOther.join_left_of_tail_contact
      prefixAvoid spokeAvoid spokeContacts
      boundaryLast spokeHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
