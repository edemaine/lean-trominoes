import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineRouteReversalContacts

/-!
# Endpoint directions of separated orthogonal polylines

Two nondegenerate axis-aligned segments that start at the same point and
travel in the same cardinal direction have overlapping relative interiors.
Consequently, continuously separated orthogonal routes that share an
endpoint must use different directions there.
-/

namespace LeanTrominoes

namespace GridSegment

/-- Two nondegenerate axis-aligned segments with the same start and directed
axis overlap immediately after that start. -/
theorem interiorsMeet_of_same_start_direction
    {start firstFinish secondFinish : Cell}
    (firstAligned :
      (GridSegment.mk start firstFinish).IsAxisAligned)
    (secondAligned :
      (GridSegment.mk start secondFinish).IsAxisAligned)
    (sameDirection :
      AxisDirection.between start firstFinish =
        AxisDirection.between start secondFinish) :
    GridSegment.InteriorsMeet
      (GridSegment.mk start firstFinish)
      (GridSegment.mk start secondFinish) := by
  have genuine :=
    AxisDirection.between_isGenuine_of_axisAligned firstAligned
  cases direction : AxisDirection.between start firstFinish with
  | invalid =>
      simp [AxisDirection.IsGenuine, direction] at genuine
  | east =>
      have firstData :=
        (AxisDirection.between_eq_east_iff
          start firstFinish).mp direction
      have secondDirection :
          AxisDirection.between start secondFinish =
            .east :=
        sameDirection.symm.trans direction
      have secondData :=
        (AxisDirection.between_eq_east_iff
          start secondFinish).mp secondDirection
      rcases start with ⟨startX, startY⟩
      rcases firstFinish with ⟨firstX, firstY⟩
      rcases secondFinish with ⟨secondX, secondY⟩
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega

  | north =>
      have firstData :=
        (AxisDirection.between_eq_north_iff
          start firstFinish).mp direction
      have secondDirection :
          AxisDirection.between start secondFinish =
            .north :=
        sameDirection.symm.trans direction
      have secondData :=
        (AxisDirection.between_eq_north_iff
          start secondFinish).mp secondDirection
      rcases start with ⟨startX, startY⟩
      rcases firstFinish with ⟨firstX, firstY⟩
      rcases secondFinish with ⟨secondX, secondY⟩
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega
  | west =>
      have firstData :=
        (AxisDirection.between_eq_west_iff
          start firstFinish).mp direction
      have secondDirection :
          AxisDirection.between start secondFinish =
            .west :=
        sameDirection.symm.trans direction
      have secondData :=
        (AxisDirection.between_eq_west_iff
          start secondFinish).mp secondDirection
      rcases start with ⟨startX, startY⟩
      rcases firstFinish with ⟨firstX, firstY⟩
      rcases secondFinish with ⟨secondX, secondY⟩
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega
  | south =>
      have firstData :=
        (AxisDirection.between_eq_south_iff
          start firstFinish).mp direction
      have secondDirection :
          AxisDirection.between start secondFinish =
            .south :=
        sameDirection.symm.trans direction
      have secondData :=
        (AxisDirection.between_eq_south_iff
          start secondFinish).mp secondDirection
      rcases start with ⟨startX, startY⟩
      rcases firstFinish with ⟨firstX, firstY⟩
      rcases secondFinish with ⟨secondX, secondY⟩
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega

/-- Two directed segments starting at opposite endpoints of one cardinal
unit edge overlap when both point through that edge toward each other. -/
theorem interiorsMeet_of_adjacent_opposite_directions
    {firstStart firstFinish secondStart secondFinish : Cell}
    {direction : AxisDirection}
    (genuine : direction.IsGenuine)
    (adjacent : secondStart = Cell.add firstStart direction.step)
    (firstDirection :
      AxisDirection.between firstStart firstFinish = direction)
    (secondDirection :
      AxisDirection.between secondStart secondFinish = direction.opposite) :
    GridSegment.InteriorsMeet
      (GridSegment.mk firstStart firstFinish)
      (GridSegment.mk secondStart secondFinish) := by
  cases direction with
  | invalid => simp [AxisDirection.IsGenuine] at genuine
  | east =>
      have firstData :=
        (AxisDirection.between_eq_east_iff
          firstStart firstFinish).mp firstDirection
      have secondData :=
        (AxisDirection.between_eq_west_iff
          secondStart secondFinish).mp (by
            simpa [AxisDirection.opposite] using secondDirection)
      rcases firstStart with ⟨firstStartX, firstStartY⟩
      rcases firstFinish with ⟨firstFinishX, firstFinishY⟩
      rcases secondStart with ⟨secondStartX, secondStartY⟩
      rcases secondFinish with ⟨secondFinishX, secondFinishY⟩
      simp [AxisDirection.step, Cell.add] at adjacent
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega
  | north =>
      have firstData :=
        (AxisDirection.between_eq_north_iff
          firstStart firstFinish).mp firstDirection
      have secondData :=
        (AxisDirection.between_eq_south_iff
          secondStart secondFinish).mp (by
            simpa [AxisDirection.opposite] using secondDirection)
      rcases firstStart with ⟨firstStartX, firstStartY⟩
      rcases firstFinish with ⟨firstFinishX, firstFinishY⟩
      rcases secondStart with ⟨secondStartX, secondStartY⟩
      rcases secondFinish with ⟨secondFinishX, secondFinishY⟩
      simp [AxisDirection.step, Cell.add] at adjacent
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega
  | west =>
      have firstData :=
        (AxisDirection.between_eq_west_iff
          firstStart firstFinish).mp firstDirection
      have secondData :=
        (AxisDirection.between_eq_east_iff
          secondStart secondFinish).mp (by
            simpa [AxisDirection.opposite] using secondDirection)
      rcases firstStart with ⟨firstStartX, firstStartY⟩
      rcases firstFinish with ⟨firstFinishX, firstFinishY⟩
      rcases secondStart with ⟨secondStartX, secondStartY⟩
      rcases secondFinish with ⟨secondFinishX, secondFinishY⟩
      simp [AxisDirection.step, Cell.add] at adjacent
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega
  | south =>
      have firstData :=
        (AxisDirection.between_eq_south_iff
          firstStart firstFinish).mp firstDirection
      have secondData :=
        (AxisDirection.between_eq_north_iff
          secondStart secondFinish).mp (by
            simpa [AxisDirection.opposite] using secondDirection)
      rcases firstStart with ⟨firstStartX, firstStartY⟩
      rcases firstFinish with ⟨firstFinishX, firstFinishY⟩
      rcases secondStart with ⟨secondStartX, secondStartY⟩
      rcases secondFinish with ⟨secondFinishX, secondFinishY⟩
      simp [AxisDirection.step, Cell.add] at adjacent
      simp [GridSegment.InteriorsMeet,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap]
      omega

end GridSegment

namespace AxisDirection

/-- Opposite direction is an injective operation, including at the total
fallback direction. -/
theorem opposite_injective : Function.Injective opposite := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [opposite]

/-- A step in the opposite direction followed by the original genuine step
returns to the starting lattice point. -/
theorem add_opposite_step_add_step
    (point : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    Cell.add
        (Cell.add point direction.opposite.step)
        direction.step =
      point := by
  rcases point with ⟨horizontal, vertical⟩
  cases direction <;>
    simp_all [IsGenuine, opposite, step, Cell.add]

end AxisDirection

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Endpoint-only listed contact is symmetric in the two routes. -/
theorem RoutesMeetOnlyAtEndpoints.symm
    {first second : List Cell}
    (meetOnly : RoutesMeetOnlyAtEndpoints first second) :
    RoutesMeetOnlyAtEndpoints second first := by
  intro secondIndex firstIndex equal
  have endpoints :=
    meetOnly firstIndex secondIndex equal.symm
  exact ⟨endpoints.2, endpoints.1⟩

/-- Two listed points on endpoint-contact-separated routes are unequal as
soon as either occurrence is known not to be an advertised route endpoint. -/
theorem routePoints_ne_of_routesMeetOnlyAtEndpoints
    {first second : List Cell}
    (meetOnly : RoutesMeetOnlyAtEndpoints first second)
    {firstPoint secondPoint : Cell}
    (firstMember : firstPoint ∈ first)
    (secondMember : secondPoint ∈ second)
    (oneInternal :
      ¬RoutePointIsEndpoint first firstPoint ∨
        ¬RoutePointIsEndpoint second secondPoint) :
    firstPoint ≠ secondPoint := by
  intro equal
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstEquation⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondEquation⟩
  have endpoints :=
    meetOnly firstIndex secondIndex
      (firstEquation.trans
        (equal.trans secondEquation.symm))
  rw [firstEquation, secondEquation] at endpoints
  exact oneInternal.elim
    (fun firstInternal => firstInternal endpoints.1)
    (fun secondInternal => secondInternal endpoints.2)

/-- Continuously separated orthogonal routes with the same initial point
must leave it in different directions. -/
theorem polylineFirstDirections_ne_of_routesAvoidEachOther
    {first second : List Cell}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (sameStart : first.head? = second.head?)
    (avoid : RoutesAvoidEachOther first second) :
    AxisDirection.polylineFirstDirection first ≠
      AxisDirection.polylineFirstDirection second := by
  cases first with
  | nil =>
      simp at firstLength
  | cons firstStart firstRest =>
      cases firstRest with
      | nil =>
          simp at firstLength
      | cons firstNext firstRest =>
          cases second with
          | nil =>
              simp at secondLength
          | cons secondStart secondRest =>
              cases secondRest with
              | nil =>
                  simp at secondLength
              | cons secondNext secondRest =>
                  have startEqual :
                      firstStart = secondStart := by
                    simpa using sameStart
                  subst secondStart
                  have firstAligned :
                      (GridSegment.mk
                        firstStart firstNext).IsAxisAligned :=
                    (List.isChain_cons_cons.mp
                      firstOrthogonal).1
                  have secondAligned :
                      (GridSegment.mk
                        firstStart secondNext).IsAxisAligned :=
                    (List.isChain_cons_cons.mp
                      secondOrthogonal).1
                  intro sameDirection
                  have noMeet :=
                    avoid.1
                      (⟨0, by simp [gridPolylineSegments]⟩ :
                        Fin
                          (gridPolylineSegments
                            (firstStart :: firstNext ::
                              firstRest)).length)
                      (⟨0, by simp [gridPolylineSegments]⟩ :
                        Fin
                          (gridPolylineSegments
                            (firstStart :: secondNext ::
                              secondRest)).length)
                  apply noMeet
                  simpa [gridPolylineSegments,
                    AxisDirection.polylineFirstDirection] using
                    GridSegment.interiorsMeet_of_same_start_direction
                      firstAligned secondAligned sameDirection

/-- Continuously separated routes whose starts are one cardinal step apart
cannot both point through the unit edge joining those starts. -/
theorem polylineFirstDirections_not_facing_of_routesAvoidEachOther
    {first second : List Cell}
    {firstStart secondStart : Cell}
    {direction : AxisDirection}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstHead : first.head? = some firstStart)
    (secondHead : second.head? = some secondStart)
    (genuine : direction.IsGenuine)
    (adjacent : secondStart = Cell.add firstStart direction.step)
    (avoids : RoutesAvoidEachOther first second) :
    AxisDirection.polylineFirstDirection first ≠ direction ∨
      AxisDirection.polylineFirstDirection second ≠ direction.opposite := by
  by_contra facing
  simp only [not_or, not_ne_iff] at facing
  rcases firstEquation : first with _ | ⟨firstPoint, firstRest⟩
  · simp [firstEquation] at firstLength
  rcases firstRest with _ | ⟨firstNext, firstTail⟩
  · simp [firstEquation] at firstLength
  rcases secondEquation : second with _ | ⟨secondPoint, secondRest⟩
  · simp [secondEquation] at secondLength
  rcases secondRest with _ | ⟨secondNext, secondTail⟩
  · simp [secondEquation] at secondLength
  have firstPointEq : firstPoint = firstStart := by
    rw [firstEquation] at firstHead
    exact Option.some.inj firstHead
  have secondPointEq : secondPoint = secondStart := by
    rw [secondEquation] at secondHead
    exact Option.some.inj secondHead
  have interiorsMeet :
      GridSegment.InteriorsMeet
        (GridSegment.mk firstPoint firstNext)
        (GridSegment.mk secondPoint secondNext) := by
    apply GridSegment.interiorsMeet_of_adjacent_opposite_directions genuine
    · simpa [firstPointEq, secondPointEq] using adjacent
    · simpa [firstEquation] using facing.1
    · simpa [secondEquation] using facing.2
  have disjoint := avoids.1
    (⟨0, by simp [firstEquation, gridPolylineSegments]⟩)
    (⟨0, by simp [secondEquation, gridPolylineSegments]⟩)
  exact disjoint (by
    simpa [firstEquation, secondEquation, gridPolylineSegments] using
      interiorsMeet)

/-- Continuously separated routes whose final points are one cardinal step
apart cannot enter those points from the intervening unit edge. -/
theorem polylineLastDirections_not_facing_of_routesAvoidEachOther
    {first second : List Cell}
    {firstFinish secondFinish : Cell}
    {direction : AxisDirection}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstLast : first.getLast? = some firstFinish)
    (secondLast : second.getLast? = some secondFinish)
    (genuine : direction.IsGenuine)
    (adjacent : secondFinish = Cell.add firstFinish direction.step)
    (avoids : RoutesAvoidEachOther first second) :
    AxisDirection.polylineLastDirection first ≠ direction.opposite ∨
      AxisDirection.polylineLastDirection second ≠ direction := by
  have reversed :=
    polylineFirstDirections_not_facing_of_routesAvoidEachOther
      (first := first.reverse) (second := second.reverse)
      (by simpa using firstLength)
      (by simpa using secondLength)
      (by simpa using firstLast)
      (by simpa using secondLast)
      genuine adjacent (routesAvoidEachOther_reverse avoids)
  rcases reversed with firstDifferent | secondDifferent
  · left
    intro equal
    apply firstDifferent
    exact AxisDirection.opposite_injective (by
      simpa [AxisDirection.polylineLastDirection] using equal)
  · right
    intro equal
    apply secondDifferent
    have oppositeEqual := congrArg AxisDirection.opposite equal
    simpa [AxisDirection.polylineLastDirection] using oppositeEqual

/-- Continuously separated orthogonal routes with the same final point
must enter it in different directions. -/
theorem polylineLastDirections_ne_of_routesAvoidEachOther
    {first second : List Cell}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (sameFinish : first.getLast? = second.getLast?)
    (avoid : RoutesAvoidEachOther first second) :
    AxisDirection.polylineLastDirection first ≠
      AxisDirection.polylineLastDirection second := by
  have reversedDirectionsDifferent :=
    polylineFirstDirections_ne_of_routesAvoidEachOther
      (first := first.reverse) (second := second.reverse)
      (by simpa using firstLength)
      (by simpa using secondLength)
      firstOrthogonal.reverse secondOrthogonal.reverse
      (by simpa using sameFinish)
      (routesAvoidEachOther_reverse avoid)
  intro sameDirection
  apply reversedDirectionsDifferent
  exact
    AxisDirection.opposite_injective
      (by
        simpa [AxisDirection.polylineLastDirection] using
          sameDirection)

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
end LeanTrominoes
