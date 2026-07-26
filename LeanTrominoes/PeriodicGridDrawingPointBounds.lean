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

/-- In a polyline with at least two points, every listed point is an endpoint
of some consecutive segment. -/
theorem exists_gridPolylineSegment_of_mem
    {points : List Cell} {point : Cell}
    (length : 2 ≤ points.length)
    (member : point ∈ points) :
    ∃ segment ∈ gridPolylineSegments points,
      segment.start = point ∨ segment.finish = point := by
  rcases points with _ | ⟨first, points⟩
  · simp at length
  rcases points with _ | ⟨second, rest⟩
  · simp at length
  induction rest generalizing first second with
  | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with pointEq | pointEq
      · subst point
        exact ⟨⟨first, second⟩, by simp [gridPolylineSegments],
          Or.inl rfl⟩
      · subst point
        exact ⟨⟨first, second⟩, by simp [gridPolylineSegments],
          Or.inr rfl⟩
  | cons third rest induction =>
      rw [List.mem_cons] at member
      rcases member with pointEq | member
      · subst point
        exact ⟨⟨first, second⟩,
          by simp [gridPolylineSegments], Or.inl rfl⟩
      · have tailMember :
            point ∈ second :: third :: rest := by
          exact member
        rcases induction (first := second) (second := third)
            (by simp) tailMember with
          ⟨segment, segmentMember, endpoint⟩
        exact
          ⟨segment,
            by
              exact List.mem_cons_of_mem
                ⟨first, second⟩ segmentMember,
            endpoint⟩

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

/-- Conversely, segment-endpoint bounds control every route point when stored
routes are nondegenerate. -/
theorem routePointsInFundamentalSquare_of_segmentEndpoints
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (routesNondegenerate :
      ∀ route ∈ drawing.edgeRoutes, 2 ≤ route.length) :
    drawing.RoutePointsInFundamentalSquare := by
  intro route routeMember point pointMember
  rcases exists_gridPolylineSegment_of_mem
      (routesNondegenerate route routeMember) pointMember with
    ⟨segment, segmentMember, endpoint⟩
  let routeIndex := drawing.edgeRoutes.idxOf route
  have routeIndexLt :
      routeIndex < drawing.edgeRoutes.length :=
    List.idxOf_lt_length_of_mem routeMember
  have routeLookup :
      drawing.edgeRoutes[routeIndex] = route :=
    List.getElem_idxOf routeIndexLt
  let segmentIndex :=
    (gridPolylineSegments route).idxOf segment
  have segmentIndexLt :
      segmentIndex < (gridPolylineSegments route).length :=
    List.idxOf_lt_length_of_mem segmentMember
  have segmentLookup :
      (gridPolylineSegments route)[segmentIndex] = segment :=
    List.getElem_idxOf segmentIndexLt
  let indexed : IndexedGridSegment :=
    ⟨routeIndex, segmentIndex, segment⟩
  have indexedMember :
      indexed ∈ drawing.indexedSegments := by
    unfold indexedSegments
    apply List.mem_flatMap.mpr
    refine
      ⟨(route, routeIndex), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨routeIndexLt, routeLookup⟩
    · apply List.mem_map.mpr
      refine ⟨(segment, segmentIndex), ?_, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨segmentIndexLt, segmentLookup⟩
  have bounds := endpointBounds indexed indexedMember
  rcases endpoint with rfl | rfl
  · exact bounds.1
  · exact bounds.2

end PeriodicGridDrawing
end LeanTrominoes
