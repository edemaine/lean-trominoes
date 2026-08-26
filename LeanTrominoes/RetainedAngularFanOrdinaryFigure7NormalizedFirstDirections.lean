/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOrdinaryFigure7HeadIsolation
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation

/-! # Normalized first directions of ordinary fallback splices -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

private theorem two_le_length_of_firstDirection_isGenuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

private theorem polylineFirstDirection_isGenuine_of_orthogonal
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal : OrthogonalPolyline points) :
    (AxisDirection.polylineFirstDirection points).IsGenuine := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          exact AxisDirection.between_isGenuine_of_axisAligned
            (List.isChain_cons_cons.mp orthogonal).1

/-- Normalizing a complete ordinary source splice, including its matching
Figure 7 spoke, preserves the original source-edge direction whenever its
twice-refined source head is absent from both appended pieces. -/
theorem
    retainedAngularFanSplicedOwnFigure7Route_normalized_firstDirection
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
    (retained : RetainedRayPolyline route)
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
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedAngularFanSplicedOwnFigure7Route
            route terminal slot (route.getLastD (0, 0)))) =
      AxisDirection.polylineFirstDirection route := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let boundary :=
    retainedAngularFanSplicedBoundaryRoute route terminal slot
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  let complete := joinAtEndpoint boundary spoke
  have boundaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      route terminal slot (by omega) classified retained routeHead
  have spokeHead :=
    retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  have spokeOrthogonal : OrthogonalPolyline spoke :=
    retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  have completeOrthogonal : OrthogonalPolyline complete := by
    exact boundaryValid.2.2.joinAtEndpoint
      spokeOrthogonal boundaryValid.2.1 spokeHead
  have completeDirection :
      AxisDirection.polylineFirstDirection complete =
        AxisDirection.polylineFirstDirection route := by
    change
      AxisDirection.polylineFirstDirection
          (retainedAngularFanSplicedOwnFigure7Route
            route terminal slot (route.getLastD (0, 0))) =
        AxisDirection.polylineFirstDirection route
    exact retainedAngularFanSplicedOwnFigure7Route_firstDirection
      route terminal slot (route.getLastD (0, 0))
      routeLength classified routeOrthogonal retained
  have routeGenuine :
      (AxisDirection.polylineFirstDirection route).IsGenuine :=
    polylineFirstDirection_isGenuine_of_orthogonal
      (by omega) routeOrthogonal
  have completeGenuine :
      (AxisDirection.polylineFirstDirection complete).IsGenuine := by
    rw [completeDirection]
    exact routeGenuine
  have completeLength : 2 ≤ complete.length :=
    two_le_length_of_firstDirection_isGenuine completeGenuine
  have fresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline complete) := by
    change
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (retainedAngularFanSplicedOwnFigure7Route
            route terminal slot (route.getLastD (0, 0))))
    exact retainedAngularFanSplicedOwnFigure7Route_headNotInTail
      route terminal slot source routeLength classified simple
      routeHead routeOrthogonal headNotInOuter headNotInSpoke
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline complete) =
      AxisDirection.polylineFirstDirection route
  calc
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline complete) =
      AxisDirection.polylineFirstDirection complete :=
        AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
          (AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
            completeLength completeOrthogonal)
          completeOrthogonal fresh
    _ = AxisDirection.polylineFirstDirection route := completeDirection

end PeriodicOrthocrossing
end LeanTrominoes
