/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackFirstDirections
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalSourceHeadSeparationSupport
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin

/-! # Ordinary fallback source-head isolation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- If the twice-refined source head is absent from an ordinary outer fan and
its matching Figure 7 spoke, it remains isolated in their complete splice. -/
theorem retainedAngularFanSplicedOwnFigure7Route_headNotInTail
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (source : Cell)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeHead : route.head? = some source)
    (routeOrthogonal : OrthogonalPolyline route)
    (headNotInOuter :
      Cell.scale retainedTerminalFanTotalRefinement source ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            terminal slot))
    (headNotInSpoke :
      Cell.scale retainedTerminalFanTotalRefinement source ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanFigure7SpokeRouteAt
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0)))
            slot)) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (retainedAngularFanSplicedOwnFigure7Route
          route terminal slot (route.getLastD (0, 0)))) := by
  let refinedRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let sourcePrefix := refinedRoute.dropLast
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let outer :=
    retainedTerminalFanOuterCompleteRoute center terminal slot
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  let sourceHead :=
    Cell.scale retainedTerminalFanTotalRefinement source
  let boundary := joinAtEndpoint sourcePrefix outer
  have refinedLength : 3 ≤ refinedRoute.length := by
    simpa [refinedRoute, scalePolyline] using routeLength
  have prefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix]
    rw [List.length_dropLast]
    omega
  have prefixNonempty : sourcePrefix ≠ [] := by
    intro empty
    rw [empty] at prefixLength
    simp at prefixLength
  have refinedHead : refinedRoute.head? = some sourceHead := by
    simpa [refinedRoute, sourceHead] using
      congrArg (Option.map
        (Cell.scale retainedTerminalFanTotalRefinement)) routeHead
  have prefixHead : sourcePrefix.head? = some sourceHead := by
    rw [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.dropLast_head?_eq_head?_of_ne_nil
      prefixNonempty]
    exact refinedHead
  have refinedOrthogonal : OrthogonalPolyline refinedRoute :=
    routeOrthogonal.scalePolyline (by native_decide)
  have prefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact refinedOrthogonal.dropLast
  have refinedSimple :
      LocalIncidenceDrawing.RouteIsSimple refinedRoute := by
    exact routeIsSimple_scalePolyline (by native_decide) simple
  have prefixSimple :
      LocalIncidenceDrawing.RouteIsSimple sourcePrefix := by
    have reversed := refinedSimple.reverse.tail.reverse
    rw [← List.dropLast_reverse (l := refinedRoute.reverse)]
      at reversed
    simpa [sourcePrefix] using reversed
  have prefixFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline sourcePrefix) :=
    AxisDirection.headNotInTail_unitSubdividePolyline_of_simple
      prefixOrthogonal prefixSimple
  have prefixLast :
      sourcePrefix.getLast? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    simpa [sourcePrefix, refinedRoute, center] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route terminal slot (by omega) classified
  have outerHead :
      outer.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      center terminal slot
  have boundaryFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline boundary) := by
    exact
      AxisDirection.HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
        prefixFresh
        prefixNonempty prefixHead prefixLast outerHead
        (by simpa [sourceHead, outer, center] using headNotInOuter)
  have boundaryHead : boundary.head? = some sourceHead :=
    joinAtEndpoint_head? prefixHead
  have boundaryNonempty : boundary ≠ [] := by
    intro empty
    rw [empty] at boundaryHead
    simp at boundaryHead
  have terminalPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have outerLast :=
    retainedTerminalFanOuterCompleteRoute_getLast?
      center terminal slot terminalPositive
  have spokeHead :=
    retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  have boundaryLast :
      boundary.getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) :=
    joinAtEndpoint_getLast? prefixLast outerHead outerLast
  have completeFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (joinAtEndpoint boundary spoke)) := by
    exact
      AxisDirection.HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
        boundaryFresh
        boundaryNonempty boundaryHead boundaryLast spokeHead
        (by simpa [sourceHead, spoke, center] using headNotInSpoke)
  have boundaryEq :
      retainedAngularFanSplicedBoundaryPolyline
          route terminal slot =
        boundary := by
    unfold retainedAngularFanSplicedBoundaryPolyline
    rw [replacePolylineTail_eq_joinAtEndpoint_dropLast
      refinedRoute outer prefixLast outerHead]
  have boundaryOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      route terminal slot (by omega) classified routeOrthogonal
  have boundaryRouteEq :
      retainedAngularFanSplicedBoundaryRoute route terminal slot =
        boundary := by
    unfold retainedAngularFanSplicedBoundaryRoute
    rw [rasterizeRetainedPolyline_eq_of_orthogonal
      boundaryOrthogonal]
    exact boundaryEq
  unfold retainedAngularFanSplicedOwnFigure7Route
  rw [boundaryRouteEq]
  exact completeFresh

end PeriodicOrthocrossing
end LeanTrominoes
