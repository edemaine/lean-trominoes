/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedCycleSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedAngularFanSourceLocalSeparation
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-!
# Copied-source splices avoid their own inner implication cycle

Route simplicity keeps a copied source route's deleted-final-point prefix
clear of its old variable endpoint.  The factor-288 fan refinement expands
that integral clearance beyond the radius-48 implication cycle.  The
ordinary and delayed-lane replacement fans avoid the same cycle by their
supporting-side certificates.

This module rejoins those pieces and then removes the no-op retained-ray
rasterization.  The resulting ordinary and escaped source-to-Figure-7
boundary routes are strictly contact-free from every route in their own
inner implication cycle.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Uniform scaling commutes with deleting a polyline's last listed point. -/
theorem scalePolyline_dropLast_eq
    (factor : Nat)
    (route : List Cell) :
    (scalePolyline factor route).dropLast =
      scalePolyline factor route.dropLast := by
  induction route with
  | nil =>
      rfl
  | cons point route induction =>
      cases route with
      | nil =>
          rfl
      | cons next rest =>
          simp [scalePolyline]

/-- Positioning a centered inner implication route preserves its radius-48
coordinate bound. -/
theorem retainedTerminalFanInnerCycleRouteAt_points_within_inner_square
    (center : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    {point : Cell}
    (pointMember :
      point ∈ retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) :
    WithinCoordinateRadius 48 center point := by
  unfold retainedTerminalFanInnerCycleRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  have bounded :=
    retainedTerminalFanInnerCycleRoute_points_within_inner_square
      vertex literalIndex offset offsetMember
  simpa [Cell.add] using bounded.translate center

/-- A simple source route's factor-288 deleted-final-point prefix strictly
avoids every implication route centered at its scaled final point. -/
theorem
    retainedAngularFanSourcePrefix_strictlyAvoids_ownInnerCycleRouteAt
    (route : List Cell)
    (finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeFinal : route.getLast? = some finalPoint) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement route).dropLast
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  have clearance :=
    routeIsSimple_dropLast_avoids_final_point
      simple routeFinal
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_pointNeighborhood
      (source := route.dropLast)
      (nearby :=
        retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex)
      (factor := retainedTerminalFanTotalRefinement)
      (radius := 48)
      (by native_decide)
      (by native_decide)
      clearance.1 clearance.2
      (fun point pointMember =>
        retainedTerminalFanInnerCycleRouteAt_points_within_inner_square
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex pointMember)
  simpa only [scalePolyline_dropLast_eq] using separated

/-- A classified source route's factor-288 prefix ends at the exact gate
where its ordinary or escaped replacement fan begins. -/
theorem retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal) :
    (scalePolyline retainedTerminalFanTotalRefinement
      route).dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot).gate := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have reverseTailExists :
      ∃ entrance, scaledRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      scaledRoute scaledLength
  have lastEntranceEq :
      polylineLastEntrance scaledRoute =
        (retainedAngularFanOuterDemand
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          terminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      routeLength classified slot
  have reverseTailHead :
      scaledRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  exact dropLast_getLast?_of_reverse_tail_head?
    reverseTailHead

/-- Before its no-op retained-ray rasterization, an ordinary copied-source
splice strictly avoids every route in its own inner implication cycle. -/
theorem
    retainedAngularFanSplicedBoundaryPolyline_strictlyAvoids_ownInnerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeFinal : route.getLast? = some finalPoint)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        route terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute
      center terminal slot
  have routeLastD :
      route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have centerEq :
      center =
        Cell.scale retainedTerminalFanTotalRefinement finalPoint := by
    exact congrArg
      (Cell.scale retainedTerminalFanTotalRefinement)
      routeLastD
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          route).dropLast
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex) :=
    retainedAngularFanSourcePrefix_strictlyAvoids_ownInnerCycleRouteAt
      route finalPoint vertex literalIndex simple routeFinal
  have lengthPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have replacementAvoid :
      RoutesStrictlyAvoidEachOther
        replacement
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex) := by
    change
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          center terminal slot)
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex)
    rw [centerEq]
    exact
      retainedTerminalFanOuterCompleteRoute_strictlyAvoid_innerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        terminal slot vertex literalIndex
        lengthPositive radialLengthPositive
  have routeEntrance :=
    retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
      route terminal slot routeLength classified
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterCompleteRoute_head?
      center terminal slot
  rw [retainedAngularFanSplicedBoundaryPolyline,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      (scalePolyline retainedTerminalFanTotalRefinement route)
      replacement routeEntrance replacementHead]
  exact prefixAvoid.join_left
    replacementAvoid routeEntrance replacementHead

/-- The ordinary rasterized copied-source splice strictly avoids every
route in its own inner implication cycle. -/
theorem
    retainedAngularFanSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryRoute
        route terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  have polylineAvoid :=
    retainedAngularFanSplicedBoundaryPolyline_strictlyAvoids_ownInnerCycleRouteAt
      route terminal slot finalPoint vertex literalIndex
      routeLength classified simple routeFinal radialLengthPositive
  have polylineOrthogonal :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified routeOrthogonal
  simpa [retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal polylineOrthogonal]
    using polylineAvoid

/-- Before its no-op retained-ray rasterization, an escaped copied-source
splice strictly avoids every route in its own inner implication cycle. -/
theorem
    retainedAngularFanEscapedSplicedBoundaryPolyline_strictlyAvoids_ownInnerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeFinal : route.getLast? = some finalPoint)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        route terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  have routeLastD :
      route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have centerEq :
      center =
        Cell.scale retainedTerminalFanTotalRefinement finalPoint := by
    exact congrArg
      (Cell.scale retainedTerminalFanTotalRefinement)
      routeLastD
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          route).dropLast
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex) :=
    retainedAngularFanSourcePrefix_strictlyAvoids_ownInnerCycleRouteAt
      route finalPoint vertex literalIndex simple routeFinal
  have lengthPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have replacementAvoid :
      RoutesStrictlyAvoidEachOther
        replacement
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex) := by
    change
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot)
        (retainedTerminalFanInnerCycleRouteAt
          (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
          vertex literalIndex)
    rw [centerEq]
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_innerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        terminal slot vertex literalIndex
        lengthPositive escapeFits
  have routeEntrance :=
    retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
      route terminal slot routeLength classified
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  rw [retainedAngularFanEscapedSplicedBoundaryPolyline,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      (scalePolyline retainedTerminalFanTotalRefinement route)
      replacement routeEntrance replacementHead]
  exact prefixAvoid.join_left
    replacementAvoid routeEntrance replacementHead

/-- The escaped rasterized copied-source splice strictly avoids every route
in its own inner implication cycle. -/
theorem
    retainedAngularFanEscapedSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (vertex : RingVertex)
    (literalIndex : Fin 2)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        vertex literalIndex) := by
  have polylineAvoid :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_strictlyAvoids_ownInnerCycleRouteAt
      route terminal slot finalPoint vertex literalIndex
      routeLength classified simple routeFinal escapeFits
  have polylineOrthogonal :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified routeOrthogonal
      escapeFits
  simpa [retainedAngularFanEscapedSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal polylineOrthogonal]
    using polylineAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
