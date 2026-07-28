import LeanTrominoes.PeriodicGridDrawing

/-!
# Indexed-segment lookup in periodic drawings

The global indexed-segment list is a flattened enumeration of each stored
route's indexed polyline segments.  These lemmas recover that two-level
presentation without depending on a particular drawing construction.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- Membership in the global indexed-segment list is equivalent to a stored
route occurrence and a same-indexed segment occurrence of that route. -/
theorem mem_indexedSegments_iff
    {drawing : PeriodicGridDrawing}
    {indexed : IndexedGridSegment} :
    indexed ∈ drawing.indexedSegments ↔
      ∃ route : List Cell,
        (route, indexed.routeIndex) ∈ drawing.edgeRoutes.zipIdx ∧
          (indexed.segment, indexed.segmentIndex) ∈
            (gridPolylineSegments route).zipIdx := by
  constructor
  · intro indexedMember
    unfold indexedSegments at indexedMember
    rcases List.mem_flatMap.mp indexedMember with
      ⟨taggedRoute, taggedRouteMember, indexedMember⟩
    rcases List.mem_map.mp indexedMember with
      ⟨taggedSegment, taggedSegmentMember, indexedEq⟩
    subst indexed
    exact
      ⟨taggedRoute.1, taggedRouteMember,
        taggedSegmentMember⟩
  · rintro ⟨route, routeMember, segmentMember⟩
    unfold indexedSegments
    apply List.mem_flatMap.mpr
    refine
      ⟨(route, indexed.routeIndex), routeMember, ?_⟩
    exact List.mem_map.mpr
      ⟨(indexed.segment, indexed.segmentIndex),
        segmentMember, rfl⟩

/-- Two indexed segments with the same route index recover a single common
stored route containing both same-indexed segment occurrences. -/
theorem exists_commonRoute_of_mem_indexedSegments_of_routeIndex_eq
    {drawing : PeriodicGridDrawing}
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    (routeIndexEq : first.routeIndex = second.routeIndex) :
    ∃ route : List Cell,
      (route, first.routeIndex) ∈ drawing.edgeRoutes.zipIdx ∧
        (first.segment, first.segmentIndex) ∈
          (gridPolylineSegments route).zipIdx ∧
        (second.segment, second.segmentIndex) ∈
          (gridPolylineSegments route).zipIdx := by
  rcases mem_indexedSegments_iff.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases mem_indexedSegments_iff.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  have firstLookup :=
    (List.mem_zipIdx_iff_getElem?).mp firstRouteMember
  have secondLookup :=
    (List.mem_zipIdx_iff_getElem?).mp secondRouteMember
  have routeEq : firstRoute = secondRoute := by
    rw [routeIndexEq, secondLookup] at firstLookup
    exact Option.some.inj firstLookup.symm
  subst secondRoute
  exact
    ⟨firstRoute, firstRouteMember,
      firstSegmentMember, secondSegmentMember⟩

end PeriodicGridDrawing
end LeanTrominoes
