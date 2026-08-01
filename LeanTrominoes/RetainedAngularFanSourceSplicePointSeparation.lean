import LeanTrominoes.RetainedAngularFanSourceSpliceBounds
import LeanTrominoes.ScaledSegmentNeighborhoodSeparation

/-!
# Separating an ordinary source splice from a bounded endpoint neighborhood

The retained source prefix and its replacement outer fan use two different
clearance arguments.  The prefix inherits point and segment avoidance from
the unscaled source route.  The fan stays in the radius-288 expansion of the
discarded final segment.  This file combines those arguments and rejoins the
two pieces, proving that the complete ordinary splice avoids any route in
the radius-96 neighborhood of another integral source endpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Uniform scaling commutes with removing the last listed point. -/
private theorem scalePolyline_dropLast
    (factor : Nat) (points : List Cell) :
    (scalePolyline factor points).dropLast =
      scalePolyline factor points.dropLast := by
  induction points with
  | nil =>
      rfl
  | cons point points induction =>
      cases points with
      | nil =>
          rfl
      | cons next rest =>
          simp [scalePolyline]

/-- An ordinary retained source/fan splice strictly avoids every route in
the radius-96 neighborhood of a scaled integral point, provided both its
retained source prefix and discarded final segment avoid that point. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryPolyline_strictlyAvoids_pointNeighborhood
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (target : Cell)
    (prefixPointsAvoid :
      ∀ point ∈ route.dropLast, point ≠ target)
    (prefixSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains target)
    (finalAligned :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (finalAvoidsTarget :
      ¬(⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          point) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal)
        slot)
      nearby := by
  let combinedFactor :=
    retainedTerminalFanTotalRefinement * factor
  let scaledRoute :=
    scalePolyline factor route
  let refinedRoute :=
    scalePolyline retainedTerminalFanTotalRefinement scaledRoute
  let scaledTerminal :=
    scaleRetainedTerminalData factor terminal
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (scaledRoute.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute
      center scaledTerminal slot
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route,
      route.getLastD (0, 0)⟩
  have combinedPositive : 0 < combinedFactor := by
    exact Nat.mul_pos (by native_decide) factorPositive
  have radiusLt : 96 < combinedFactor := by
    omega
  have prefixAvoid :
      RoutesStrictlyAvoidEachOther
        refinedRoute.dropLast nearby := by
    have separated :=
      routesStrictlyAvoidEachOther_scalePolyline_rectangleNeighborhood
        (source := route.dropLast)
        (nearby := nearby)
        (referenceLower := target)
        (referenceUpper := target)
        combinedPositive radiusLt
        (fun point pointMember =>
          closedGridSingletons_separated_of_ne
            (prefixPointsAvoid point pointMember))
        (fun segment segmentMember aligned =>
          segment.coordinateRectangle_separated_point
            aligned
            (prefixSegmentsAvoid
              segment segmentMember aligned))
        nearbyBounded
    change
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor route)).dropLast
        nearby
    rw [scalePolyline_dropLast
      retainedTerminalFanTotalRefinement
      (scalePolyline factor route)]
    rw [scalePolyline_dropLast factor route,
      scalePolyline_scalePolyline_nat]
    simpa [combinedFactor] using separated
  have replacementAvoid :
      RoutesStrictlyAvoidEachOther replacement nearby := by
    apply
      routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
        (firstLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor
              finalSegment.coordinateLower))
        (firstUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor
              finalSegment.coordinateUpper))
        (secondLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor target))
        (secondUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor target))
    · intro point pointMember
      exact
        retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
          route terminal slot routeLength classified
          (by simpa [replacement, center, scaledRoute] using
            pointMember)
    · intro point pointMember
      exact
        inClosedGridRectangle_coordinateRadius_mono
          (nearbyBounded point pointMember)
          (by omega)
    · exact
        ClosedGridRectanglesSeparated.scale_both_coordinateRadius
          (finalSegment.coordinateRectangle_separated_point
            (by simpa [finalSegment] using finalAligned)
            (by simpa [finalSegment] using finalAvoidsTarget))
          combinedPositive clearance
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have refinedLength : 2 ≤ refinedRoute.length := by
    simpa [refinedRoute, scalePolyline] using scaledLength
  have reverseTailExists :
      ∃ entrance, refinedRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      refinedRoute refinedLength
  have lastEntranceEq :
      polylineLastEntrance refinedRoute =
        (retainedAngularFanOuterDemand
          center scaledTerminal slot).gate := by
    exact
      polylineLastEntrance_scalePolyline_eq_outerDemand_gate
        scaledLength scaledClassified slot
  have reverseTailHead :
      refinedRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have routeEntrance :
      refinedRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    retainedTerminalFanOuterCompleteRoute_head?
      center scaledTerminal slot
  rw [retainedAngularFanSplicedBoundaryPolyline,
    show
      scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor route) =
        refinedRoute by rfl,
    show
      retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal) slot =
        replacement by rfl,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      refinedRoute replacement routeEntrance replacementHead]
  exact
    prefixAvoid.join_left replacementAvoid
      routeEntrance replacementHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
