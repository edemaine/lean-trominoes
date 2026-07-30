import LeanTrominoes.PeriodicGridDrawingRibbonSeparation
import LeanTrominoes.PeriodicGridDrawingVertexCoverage

/-!
# Complete separation of nonorthogonal route occurrences

The retained planar-SAT source contains diagonal rays, so the orthogonal
route-occurrence separation theorem is not directly applicable.  The final
retained drawing carries the stronger `SegmentEndpointsAvoidInteriors`
certificate.  Every listed point of a route of length at least two is an
endpoint of an incident segment, so that certificate supplies both directed
point/interior conditions without assuming the route is orthogonal.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PlanarThreeSAT

private theorem segmentOccurrenceKey_ne_of_routeOccurrence_ne'
    {firstRouteIndex secondRouteIndex : Nat}
    {firstSegmentIndex secondSegmentIndex : Nat}
    {firstSegment secondSegment : GridSegment}
    {firstTranslate secondTranslate : Cell}
    (different :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    SegmentOccurrenceKey
        ⟨firstRouteIndex, firstSegmentIndex, firstSegment⟩
        firstTranslate ≠
      SegmentOccurrenceKey
        ⟨secondRouteIndex, secondSegmentIndex, secondSegment⟩
        secondTranslate := by
  intro equal
  apply different
  simp only [SegmentOccurrenceKey, Prod.mk.injEq] at equal ⊢
  exact ⟨equal.1, equal.2.2⟩

private theorem routePointOccurrenceKey_ne_of_routeOccurrence_ne'
    {firstRouteIndex secondRouteIndex : Nat}
    {firstPointIndex secondPointIndex : Nat}
    {firstTranslate secondTranslate : Cell}
    (different :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    RoutePointOccurrenceKey
        { routeIndex := firstRouteIndex
          pointIndex := firstPointIndex
          routeLength := 0
          point := (0, 0) }
        firstTranslate ≠
      RoutePointOccurrenceKey
        { routeIndex := secondRouteIndex
          pointIndex := secondPointIndex
          routeLength := 0
          point := (0, 0) }
        secondTranslate := by
  intro equal
  apply different
  simp only [RoutePointOccurrenceKey, Prod.mk.injEq] at equal ⊢
  exact ⟨equal.1, equal.2.2⟩

/-- A listed point of one nondegenerate route avoids the interior of every
segment of a distinct lifted route occurrence. -/
theorem routePoint_avoids_segmentInterior_of_segmentEndpointsAvoid
    {drawing : PeriodicGridDrawing}
    (endpointsAvoid : drawing.SegmentEndpointsAvoidInteriors)
    {route otherRoute : List Cell}
    {routeIndex otherRouteIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    (otherRouteMember :
      (otherRoute, otherRouteIndex) ∈ drawing.edgeRoutes.zipIdx)
    (routeLength : 2 ≤ route.length)
    (routeTranslate otherTranslate : Cell)
    (occurrencesDifferent :
      (routeIndex, routeTranslate) ≠
        (otherRouteIndex, otherTranslate))
    (pointIndex : Fin route.length)
    (segmentIndex :
      Fin (gridPolylineSegments otherRoute).length) :
    ¬((gridPolylineSegments otherRoute).get segmentIndex
        |>.translate
          (drawing.periodTranslation otherTranslate)).InteriorContains
      (Cell.add
        (drawing.periodTranslation routeTranslate)
        (route.get pointIndex)) := by
  rcases
      PeriodicOrthocrossing.exists_segment_endpoint_of_mem
        routeLength (List.get_mem route pointIndex) with
    ⟨incident, incidentMember, pointEndpoint⟩
  rcases List.mem_iff_get.mp incidentMember with
    ⟨incidentIndex, incidentEqual⟩
  let incidentIndexed : IndexedGridSegment :=
    ⟨routeIndex, incidentIndex,
      (gridPolylineSegments route).get incidentIndex⟩
  let otherIndexed : IndexedGridSegment :=
    ⟨otherRouteIndex, segmentIndex,
      (gridPolylineSegments otherRoute).get segmentIndex⟩
  have incidentIndexedMember :
      incidentIndexed ∈ drawing.indexedSegments :=
    indexedSegment_mem_of_route_mem routeMember incidentIndex
  have otherIndexedMember :
      otherIndexed ∈ drawing.indexedSegments :=
    indexedSegment_mem_of_route_mem
      otherRouteMember segmentIndex
  have different :
      SegmentOccurrenceKey otherIndexed otherTranslate ≠
        SegmentOccurrenceKey incidentIndexed routeTranslate :=
    segmentOccurrenceKey_ne_of_routeOccurrence_ne'
      (Ne.symm occurrencesDifferent)
  intro interior
  have avoids :=
    endpointsAvoid
      otherIndexed otherIndexedMember
      incidentIndexed incidentIndexedMember
      otherTranslate routeTranslate
      (Cell.add
        (drawing.periodTranslation routeTranslate)
        (route.get pointIndex))
      different
      (by simpa [otherIndexed] using interior)
  rcases pointEndpoint with pointStart | pointFinish
  · apply avoids.1
    have original :
        route.get pointIndex =
          ((gridPolylineSegments route).get incidentIndex).start := by
      rw [incidentEqual]
      exact pointStart
    simpa [incidentIndexed, GridSegment.translate] using
      congrArg
        (Cell.add (drawing.periodTranslation routeTranslate))
        original
  · apply avoids.2
    have original :
        route.get pointIndex =
          ((gridPolylineSegments route).get incidentIndex).finish := by
      rw [incidentEqual]
      exact pointFinish
    simpa [incidentIndexed, GridSegment.translate] using
      congrArg
        (Cell.add (drawing.periodTranslation routeTranslate))
        original

/-- Distinct lifted occurrences of possibly diagonal routes satisfy the
finite complete route-separation predicate when the drawing supplies
continuous segment separation, endpoint-aware separation, and endpoint-only
listed contacts. -/
theorem routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
    {drawing : PeriodicGridDrawing}
    (continuous : drawing.IsContinuouslyPlanar)
    (segmentEndpointsAvoid :
      drawing.SegmentEndpointsAvoidInteriors)
    (endpointContacts :
      drawing.RoutePointsMeetOnlyAtEndpoints)
    {first second : List Cell}
    {firstRouteIndex secondRouteIndex : Nat}
    (firstRouteMember :
      (first, firstRouteIndex) ∈ drawing.edgeRoutes.zipIdx)
    (secondRouteMember :
      (second, secondRouteIndex) ∈ drawing.edgeRoutes.zipIdx)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstTranslate secondTranslate : Cell)
    (occurrencesDifferent :
      (firstRouteIndex, firstTranslate) ≠
        (secondRouteIndex, secondTranslate)) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (first.map
        (Cell.add (drawing.periodTranslation firstTranslate)))
      (second.map
        (Cell.add (drawing.periodTranslation secondTranslate))) := by
  let firstOffset := drawing.periodTranslation firstTranslate
  let secondOffset := drawing.periodTranslation secondTranslate
  unfold EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    let firstOriginalIndex :
        Fin (gridPolylineSegments first).length :=
      ⟨firstIndex, by
        simpa [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using firstIndex.isLt⟩
    let secondOriginalIndex :
        Fin (gridPolylineSegments second).length :=
      ⟨secondIndex, by
        simpa [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using secondIndex.isLt⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨firstRouteIndex, firstOriginalIndex,
        (gridPolylineSegments first).get firstOriginalIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨secondRouteIndex, secondOriginalIndex,
        (gridPolylineSegments second).get secondOriginalIndex⟩
    have firstMember :
        firstIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        firstRouteMember firstOriginalIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedSegments :=
      indexedSegment_mem_of_route_mem
        secondRouteMember secondOriginalIndex
    have different :
        SegmentOccurrenceKey firstIndexed firstTranslate ≠
          SegmentOccurrenceKey secondIndexed secondTranslate :=
      segmentOccurrenceKey_ne_of_routeOccurrence_ne'
        occurrencesDifferent
    have disjoint :=
      continuous.noInteriorsMeet
        firstMember secondMember different
    simpa [firstIndexed, secondIndexed, firstOffset, secondOffset,
      firstOriginalIndex, secondOriginalIndex,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
      using disjoint
  · intro firstPointIndex secondSegmentIndex
    let firstOriginalPointIndex : Fin first.length :=
      ⟨firstPointIndex, by simpa using firstPointIndex.isLt⟩
    let secondOriginalSegmentIndex :
        Fin (gridPolylineSegments second).length :=
      ⟨secondSegmentIndex, by
        simpa [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using secondSegmentIndex.isLt⟩
    have avoids :=
      routePoint_avoids_segmentInterior_of_segmentEndpointsAvoid
        segmentEndpointsAvoid
        firstRouteMember secondRouteMember firstLength
        firstTranslate secondTranslate occurrencesDifferent
        firstOriginalPointIndex secondOriginalSegmentIndex
    simpa [firstOffset, secondOffset, firstOriginalPointIndex,
      secondOriginalSegmentIndex,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
      using avoids
  · intro secondPointIndex firstSegmentIndex
    let secondOriginalPointIndex : Fin second.length :=
      ⟨secondPointIndex, by simpa using secondPointIndex.isLt⟩
    let firstOriginalSegmentIndex :
        Fin (gridPolylineSegments first).length :=
      ⟨firstSegmentIndex, by
        simpa [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
          using firstSegmentIndex.isLt⟩
    have avoids :=
      routePoint_avoids_segmentInterior_of_segmentEndpointsAvoid
        segmentEndpointsAvoid
        secondRouteMember firstRouteMember secondLength
        secondTranslate firstTranslate
        (Ne.symm occurrencesDifferent)
        secondOriginalPointIndex firstOriginalSegmentIndex
    simpa [firstOffset, secondOffset, secondOriginalPointIndex,
      firstOriginalSegmentIndex,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
      using avoids
  · intro firstPointIndex secondPointIndex pointEqual
    let firstOriginalPointIndex : Fin first.length :=
      ⟨firstPointIndex, by simpa using firstPointIndex.isLt⟩
    let secondOriginalPointIndex : Fin second.length :=
      ⟨secondPointIndex, by simpa using secondPointIndex.isLt⟩
    let firstIndexed : IndexedRoutePoint :=
      { routeIndex := firstRouteIndex
        pointIndex := firstOriginalPointIndex
        routeLength := first.length
        point := first.get firstOriginalPointIndex }
    let secondIndexed : IndexedRoutePoint :=
      { routeIndex := secondRouteIndex
        pointIndex := secondOriginalPointIndex
        routeLength := second.length
        point := second.get secondOriginalPointIndex }
    have firstMember :
        firstIndexed ∈ drawing.indexedRoutePoints :=
      indexedRoutePoint_mem_of_route_mem
        firstRouteMember firstOriginalPointIndex
    have secondMember :
        secondIndexed ∈ drawing.indexedRoutePoints :=
      indexedRoutePoint_mem_of_route_mem
        secondRouteMember secondOriginalPointIndex
    have different :
        RoutePointOccurrenceKey firstIndexed firstTranslate ≠
          RoutePointOccurrenceKey secondIndexed secondTranslate :=
      routePointOccurrenceKey_ne_of_routeOccurrence_ne'
        occurrencesDifferent
    have physicalEqual :
        Cell.add firstIndexed.point firstOffset =
          Cell.add secondIndexed.point secondOffset := by
      simpa [firstIndexed, secondIndexed, firstOffset,
        secondOffset, firstOriginalPointIndex,
        secondOriginalPointIndex, Cell.add,
        add_comm] using pointEqual
    have outer :=
      endpointContacts firstIndexed firstMember
        secondIndexed secondMember
        firstTranslate secondTranslate different
        (by simpa [firstOffset, secondOffset] using physicalEqual)
    constructor
    · exact
        routePointIsEndpoint_of_index firstPointIndex
          (by
            simpa [firstIndexed, firstOriginalPointIndex,
              IndexedRoutePoint.IsEndpoint] using outer.1)
    · exact
        routePointIsEndpoint_of_index secondPointIndex
          (by
            simpa [secondIndexed, secondOriginalPointIndex,
              IndexedRoutePoint.IsEndpoint] using outer.2)

end PeriodicGridDrawing
end LeanTrominoes
