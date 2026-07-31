import LeanTrominoes.RetainedAngularFanSourceRadialSeparation
import LeanTrominoes.RetainedRayRasterizationSeparation

/-!
# Outer-fan separation inherited from source terminal segments

Every complete outer fan stays in the radius-288 expansion of the combined-
scaled endpoint rectangle of the discarded source terminal segment.  Thus
one lattice unit of rectangular separation between two source terminals
becomes enough clearance, after source-first refinement, to separate their
complete outer fans.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Enlarging both coordinate-radius margins preserves membership in the
expanded rectangle. -/
theorem inClosedGridRectangle_coordinateRadius_mono
    {smaller larger : Nat}
    {lower upper point : Cell}
    (bounded :
      InClosedGridRectangle
        (coordinateRadiusLower smaller lower)
        (coordinateRadiusUpper smaller upper)
        point)
    (radiusLe : smaller ≤ larger) :
    InClosedGridRectangle
      (coordinateRadiusLower larger lower)
      (coordinateRadiusUpper larger upper)
      point := by
  rcases lower with ⟨lowerX, lowerY⟩
  rcases upper with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper] at bounded ⊢
  omega

/-- A radius-bounded point around any center in a rectangle belongs to the
same radius expansion of that rectangle. -/
theorem inClosedGridRectangle_coordinateRadius_of_center
    {radius : Nat}
    {lower upper center point : Cell}
    (centerBounded :
      InClosedGridRectangle lower upper center)
    (pointBounded :
      WithinCoordinateRadius radius center point) :
    InClosedGridRectangle
      (coordinateRadiusLower radius lower)
      (coordinateRadiusUpper radius upper)
      point := by
  rcases lower with ⟨lowerX, lowerY⟩
  rcases upper with ⟨upperX, upperY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases pointBounded.coordinate_bounds with
    ⟨horizontal, vertical⟩
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper]
    at centerBounded ⊢
  omega

/-- Every point of a complete outer fan lies in the radius-288 expansion of
the combined-scaled endpoint rectangle of its discarded source segment. -/
theorem
    retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal)
          slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper))
      point := by
  rw [retainedTerminalFanOuterCompleteRoute] at pointMember
  rcases mem_joinAtEndpoint pointMember with
    radialMember | localMember
  · exact
      inClosedGridRectangle_coordinateRadius_mono
        (retainedTerminalFanOuterRadialRoute_point_in_scaledFinalSegmentRectangle
          route terminal slot routeLength classified radialMember)
        (by omega)
  · have productNonnegative :
        (0 : Int) ≤
          retainedTerminalFanTotalRefinement * factor := by
      exact_mod_cast
        Nat.zero_le
          (retainedTerminalFanTotalRefinement * factor)
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    have centerBounded :
        InClosedGridRectangle
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateLower)
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateUpper)
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0))) := by
      have finishBounded :=
        finalSegment.finish_in_coordinateRectangle.scale
          productNonnegative
      rw [scalePolyline_getLastD, Cell.scale_scale]
      simpa [finalSegment, Nat.cast_mul] using finishBounded
    have localBounded :
        WithinCoordinateRadius 288
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          point := by
      rw [retainedTerminalFanOuterLocalRouteAt,
        List.mem_map] at localMember
      rcases localMember with
        ⟨offset, offsetMember, rfl⟩
      have offsetBounded :=
        retainedTerminalFanOuterLocalRoute_points_within_outer_frame
          (scaleRetainedTerminalData factor terminal).1
          slot offset offsetMember
      simpa [Cell.add] using
        offsetBounded.translate
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
    simpa [finalSegment] using
      inClosedGridRectangle_coordinateRadius_of_center
        centerBounded localBounded

/-- Rectangular separation of two discarded source terminal segments
survives the combined source and fan refinement as strict separation of
their complete outer routes. -/
theorem
    retainedTerminalFanOuterCompleteRoutes_strictlyAvoid_of_finalSegmentRectanglesSeparated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor firstRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor secondRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have combinedPositive :
      0 <
        retainedTerminalFanTotalRefinement * factor :=
    Nat.mul_pos (by native_decide) factorPositive
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
  · intro point pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        firstRoute firstTerminal firstSlot
        firstLength firstClassified pointMember
  · intro point pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        secondRoute secondTerminal secondSlot
        secondLength secondClassified pointMember
  · exact
      LeanTrominoes.PeriodicEightOccurrenceSplit.ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        rectanglesSeparated combinedPositive clearance

end PeriodicEightOccurrenceSplit
end LeanTrominoes
