/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-!
# Strict separation assembly for fallback boundary routes

The ordinary and delayed-lane fallback boundaries replace the last point of
a scaled retained source route by an outer fan, then rasterize the resulting
orthogonal polyline.  These theorems expose that common construction as a
two-piece strict-separation interface.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Strict avoidance of the refined retained prefix and of the ordinary
outer replacement assembles into strict avoidance of the rasterized fallback
boundary route. -/
theorem
    strictlyAvoids_retainedAngularFanSplicedBoundaryRoute_of_prefix_replacement
    (other route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (prefixAvoid :
      RoutesStrictlyAvoidEachOther other
        (scalePolyline retainedTerminalFanTotalRefinement route).dropLast)
    (replacementAvoid :
      RoutesStrictlyAvoidEachOther other
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          terminal slot)) :
    RoutesStrictlyAvoidEachOther other
      (retainedAngularFanSplicedBoundaryRoute
        route terminal slot) := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute
      center terminal slot
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
          center terminal slot).gate := by
    exact
      polylineLastEntrance_scalePolyline_eq_outerDemand_gate
        routeLength classified slot
  have reverseTailHead :
      scaledRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have routeEntrance :
      scaledRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head? reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterCompleteRoute_head?
      center terminal slot
  have polylineEq :
      retainedAngularFanSplicedBoundaryPolyline
          route terminal slot =
        joinAtEndpoint scaledRoute.dropLast replacement := by
    rw [retainedAngularFanSplicedBoundaryPolyline,
      show
        scalePolyline retainedTerminalFanTotalRefinement route =
          scaledRoute by rfl,
      show
        retainedTerminalFanOuterCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot =
          replacement by rfl,
      replacePolylineTail_eq_joinAtEndpoint_dropLast
        scaledRoute replacement routeEntrance replacementHead]
  have joined :
      RoutesStrictlyAvoidEachOther other
        (joinAtEndpoint scaledRoute.dropLast replacement) :=
    prefixAvoid.join_right replacementAvoid
      routeEntrance replacementHead
  have polylineOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified routeOrthogonal
  rw [retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal
      polylineOrthogonal,
    polylineEq]
  exact joined

/-- Delayed-lane counterpart of the ordinary fallback boundary assembly. -/
theorem
    strictlyAvoids_retainedAngularFanEscapedSplicedBoundaryRoute_of_prefix_replacement
    (other route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (prefixAvoid :
      RoutesStrictlyAvoidEachOther other
        (scalePolyline retainedTerminalFanTotalRefinement route).dropLast)
    (replacementAvoid :
      RoutesStrictlyAvoidEachOther other
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          terminal slot)) :
    RoutesStrictlyAvoidEachOther other
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot) := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
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
          center terminal slot).gate := by
    exact
      polylineLastEntrance_scalePolyline_eq_outerDemand_gate
        routeLength classified slot
  have reverseTailHead :
      scaledRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have routeEntrance :
      scaledRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head? reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  have polylineEq :
      retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot =
        joinAtEndpoint scaledRoute.dropLast replacement := by
    rw [retainedAngularFanEscapedSplicedBoundaryPolyline,
      show
        scalePolyline retainedTerminalFanTotalRefinement route =
          scaledRoute by rfl,
      show
        retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot =
          replacement by rfl,
      replacePolylineTail_eq_joinAtEndpoint_dropLast
        scaledRoute replacement routeEntrance replacementHead]
  have joined :
      RoutesStrictlyAvoidEachOther other
        (joinAtEndpoint scaledRoute.dropLast replacement) :=
    prefixAvoid.join_right replacementAvoid
      routeEntrance replacementHead
  have polylineOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot) :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      route terminal slot routeLength classified
      routeOrthogonal escapeFits
  rw [retainedAngularFanEscapedSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal
      polylineOrthogonal,
    polylineEq]
  exact joined

end PeriodicEightOccurrenceSplit
end LeanTrominoes
