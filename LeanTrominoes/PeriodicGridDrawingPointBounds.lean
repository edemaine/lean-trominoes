import LeanTrominoes.PeriodicGridDrawingFinitePlanarity
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Route-point bounds for periodic grid drawings

Finite periodic planarity certificates phrase their coordinate hypothesis in
terms of indexed segment endpoints.  Constructed drawings are easier to
analyze one route component at a time, by showing that every listed polyline
point lies in the fundamental square.

This file proves the generic conversion.  It also records the elementary
membership rule for `joinAtEndpoint`, so bounds for independently constructed
route pieces compose without unfolding the splice repeatedly.
-/

namespace LeanTrominoes

/-- Both endpoints of every consecutive segment occur in the original
polyline point list. -/
theorem gridPolylineSegments_endpoints_mem
    {points : List Cell} {segment : GridSegment}
    (member : segment ∈ gridPolylineSegments points) :
    segment.start ∈ points ∧ segment.finish ∈ points := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [gridPolylineSegments] at member
  | singleton point =>
      simp [gridPolylineSegments] at member
  | cons_cons first second rest _ tailInduction =>
      simp only [gridPolylineSegments, List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have endpoints :=
          tailInduction second member
        exact
          ⟨List.mem_cons_of_mem first endpoints.1,
            List.mem_cons_of_mem first endpoints.2⟩

/-- Every point of a joined route comes from one of its two pieces. -/
theorem mem_joinAtEndpoint
    {first second : List Cell} {point : Cell}
    (member : point ∈ joinAtEndpoint first second) :
    point ∈ first ∨ point ∈ second := by
  rw [joinAtEndpoint, List.mem_append] at member
  rcases member with member | member
  · exact Or.inl member
  · exact Or.inr (List.mem_of_mem_tail member)

namespace PeriodicGridDrawing

/-- Pointwise version of the route-coordinate hypothesis used by the finite
periodic planarity checker. -/
def RoutePointsInFundamentalSquare
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ route ∈ drawing.edgeRoutes,
    ∀ point ∈ route,
      drawing.PositionInFundamentalSquare point

/-- Pointwise route bounds imply bounds for both endpoints of every indexed
segment occurrence. -/
theorem segmentEndpointsInFundamentalSquare_of_routePoints
    {drawing : PeriodicGridDrawing}
    (pointsInside : drawing.RoutePointsInFundamentalSquare) :
    drawing.SegmentEndpointsInFundamentalSquare := by
  intro indexed indexedMember
  unfold indexedSegments at indexedMember
  rcases List.mem_flatMap.mp indexedMember with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedSegment, taggedSegmentMember, indexedEqual⟩
  subst indexed
  have routeMember :
      taggedRoute.1 ∈ drawing.edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMember
  have segmentMember :
      taggedSegment.1 ∈
        gridPolylineSegments taggedRoute.1 :=
    List.fst_mem_of_mem_zipIdx taggedSegmentMember
  have endpointMembers :=
    gridPolylineSegments_endpoints_mem segmentMember
  exact
    ⟨pointsInside taggedRoute.1 routeMember
        taggedSegment.1.start endpointMembers.1,
      pointsInside taggedRoute.1 routeMember
        taggedSegment.1.finish endpointMembers.2⟩

end PeriodicGridDrawing
end LeanTrominoes
