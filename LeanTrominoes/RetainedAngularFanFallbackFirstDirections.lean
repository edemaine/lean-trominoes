/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceCompleteOwnCycleSeparation
import LeanTrominoes.RetainedRayRasterizationFirstDirections

/-! # Clause-side directions of ordinary angular-fan fallbacks

An ordinary fallback replaces only the final point of a retained source
route.  When the deleted-final-point prefix still contains an edge, the
source edge survives tail replacement, retained-ray rasterization, and the
final Figure 7 suffix join.  Thus its public clause-side direction is exactly
the direction of the already orthogonal source route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

private theorem polylineFirstDirection_isGenuine_of_orthogonal
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (AxisDirection.polylineFirstDirection points).IsGenuine := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second rest =>
          exact AxisDirection.between_isGenuine_of_axisAligned
            (List.isChain_cons_cons.mp orthogonal).1

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

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => rfl

private theorem polylineFirstDirection_dropLast_of_three_le_length
    {points : List Cell}
    (length : 3 ≤ points.length) :
    AxisDirection.polylineFirstDirection points.dropLast =
      AxisDirection.polylineFirstDirection points := by
  cases points with
  | nil => simp at length
  | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second tail =>
          cases tail with
          | nil => simp at length
          | cons third rest =>
              rw [List.dropLast_cons_cons,
                List.dropLast_cons_cons]
              rfl

/-- Before rasterization, ordinary tail replacement preserves the first
direction of every orthogonal source route with a two-point retained prefix.
-/
theorem retainedAngularFanSplicedBoundaryPolyline_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanSplicedBoundaryPolyline
          route terminal slot) =
      AxisDirection.polylineFirstDirection route := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute center terminal slot
  have scaledLength : 3 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have reverseTailExists :
      ∃ entrance, scaledRoute.reverse.tail.head? = some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      scaledRoute (by omega)
  have lastEntranceEq :
      polylineLastEntrance scaledRoute =
        (retainedAngularFanOuterDemand
          center terminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      (by omega) classified slot
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
            center terminal slot).gate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      center terminal slot
  have scaledOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline scaledRoute :=
    routeOrthogonal.scalePolyline (by native_decide)
  rw [retainedAngularFanSplicedBoundaryPolyline,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      scaledRoute replacement routeEntrance replacementHead,
    polylineFirstDirection_joinAtEndpoint_of_genuine]
  · rw [polylineFirstDirection_dropLast_of_three_le_length
      scaledLength]
    exact AxisDirection.polylineFirstDirection_scalePolyline
      retainedTerminalFanTotalRefinement
      (by native_decide) route
  · rw [polylineFirstDirection_dropLast_of_three_le_length
      scaledLength]
    exact polylineFirstDirection_isGenuine_of_orthogonal
      (by omega) scaledOrthogonal

/-- Retained-ray rasterization leaves the ordinary fallback's preserved
clause-side direction unchanged. -/
theorem retainedAngularFanSplicedBoundaryRoute_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (retained : RetainedRayPolyline route) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanSplicedBoundaryRoute
          route terminal slot) =
      AxisDirection.polylineFirstDirection route := by
  let boundary :=
    retainedAngularFanSplicedBoundaryPolyline route terminal slot
  have boundaryDirection :=
    retainedAngularFanSplicedBoundaryPolyline_firstDirection
      route terminal slot routeLength classified routeOrthogonal
  have sourceGenuine :=
    polylineFirstDirection_isGenuine_of_orthogonal
      (by omega) routeOrthogonal
  have boundaryGenuine :
      (AxisDirection.polylineFirstDirection boundary).IsGenuine := by
    rw [boundaryDirection]
    exact sourceGenuine
  have boundaryLength : 2 ≤ boundary.length :=
    two_le_length_of_firstDirection_isGenuine boundaryGenuine
  have boundaryOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline boundary := by
    simpa [boundary] using
      retainedAngularFanSplicedBoundaryPolyline_orthogonal
        route terminal slot (by omega) classified routeOrthogonal
  have boundaryRetained : RetainedRayPolyline boundary := by
    simpa [boundary] using
      retainedAngularFanSplicedBoundaryPolyline_retained
        route terminal slot (by omega) classified retained
  unfold retainedAngularFanSplicedBoundaryRoute
  rw [rasterizeRetainedPolyline_firstDirection_eq
    boundaryLength boundaryOrthogonal boundaryRetained]
  exact boundaryDirection

/-- Appending any suffix to the ordinary rasterized fallback preserves its
clause-side direction. -/
theorem retainedAngularFanSplicedBoundaryRoute_joinAtEndpoint_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (suffix : List Cell)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (retained : RetainedRayPolyline route) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint
          (retainedAngularFanSplicedBoundaryRoute route terminal slot)
          suffix) =
      AxisDirection.polylineFirstDirection route := by
  rw [polylineFirstDirection_joinAtEndpoint_of_genuine]
  · exact retainedAngularFanSplicedBoundaryRoute_firstDirection
      route terminal slot routeLength classified routeOrthogonal retained
  · rw [retainedAngularFanSplicedBoundaryRoute_firstDirection
      route terminal slot routeLength classified routeOrthogonal retained]
    exact polylineFirstDirection_isGenuine_of_orthogonal
      (by omega) routeOrthogonal

/-- Appending the centered Figure 7 spoke also preserves the ordinary
fallback's clause-side direction. -/
theorem retainedAngularFanSplicedOwnFigure7Route_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (retained : RetainedRayPolyline route) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint) =
      AxisDirection.polylineFirstDirection route := by
  unfold retainedAngularFanSplicedOwnFigure7Route
  exact
    retainedAngularFanSplicedBoundaryRoute_joinAtEndpoint_firstDirection
      route terminal slot _ routeLength classified routeOrthogonal retained

end PeriodicEightOccurrenceSplit
end LeanTrominoes
