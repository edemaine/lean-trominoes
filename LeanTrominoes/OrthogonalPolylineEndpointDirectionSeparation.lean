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
