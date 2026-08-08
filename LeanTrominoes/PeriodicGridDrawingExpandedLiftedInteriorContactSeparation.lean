import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity
import LeanTrominoes.PeriodicGridDrawingLiftedInteriorContactSeparation
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Finite translated-route contact reduction for halo-bounded drawings

For stored route points in the open one-cell halo, a segment-interior
contact between two route occurrences can happen only at one of the 25
relative shifts in `doubleNeighborTranslations`.  Consequently the
nonzero lifted-route separation obligation reduces to the 24 nonzero
members of that finite list.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicPlanarOneInThreeToThreeDM

/-- The finite part of nonzero relative lifted-route separation: check only
the nonzero members of the `5 × 5` halo-neighbor list. -/
def DoubleNeighborNonzeroRelativeLiftedRoutesAvoidInteriorContacts
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.edgeRoutes.zipIdx,
    ∀ second ∈ drawing.edgeRoutes.zipIdx,
      ∀ relativeTranslate ∈ doubleNeighborTranslations,
        relativeTranslate ≠ (0, 0) →
          RoutesAvoidInteriorContacts
            first.1
            (second.1.map
              (Cell.add
                (drawing.periodTranslation relativeTranslate)))

private theorem exists_indexedSegment_of_routeSegment_mem
    {drawing : PeriodicGridDrawing}
    {route : List Cell} {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    {segment : GridSegment}
    (segmentMember : segment ∈ gridPolylineSegments route) :
    ∃ indexed : IndexedGridSegment,
      indexed.segment = segment ∧
        indexed ∈ drawing.indexedSegments := by
  rcases List.mem_iff_get.mp segmentMember with ⟨segmentIndex, rfl⟩
  exact
    ⟨⟨routeIndex, segmentIndex,
        (gridPolylineSegments route).get segmentIndex⟩,
      rfl, indexedSegment_mem_of_route_mem routeMember segmentIndex⟩

/-- Outside the 25 halo-neighbor shifts, two stored routes automatically
avoid every form of segment-interior contact. -/
theorem routesAvoidInteriorContacts_of_not_doubleNeighbor
    {drawing : PeriodicGridDrawing}
    (pointBounds : drawing.RoutePointsInExpandedSquare)
    {first second : List Cell} {firstIndex secondIndex : Nat}
    (firstMember :
      (first, firstIndex) ∈ drawing.edgeRoutes.zipIdx)
    (secondMember :
      (second, secondIndex) ∈ drawing.edgeRoutes.zipIdx)
    {relativeTranslate : Cell}
    (relativeOutside :
      relativeTranslate ∉ doubleNeighborTranslations) :
    RoutesAvoidInteriorContacts
      first
      (second.map
        (Cell.add
          (drawing.periodTranslation relativeTranslate))) := by
  let offset := drawing.periodTranslation relativeTranslate
  have endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare :=
    segmentEndpointsInExpandedSquare_of_routePoints pointBounds
  have firstRouteMember : first ∈ drawing.edgeRoutes :=
    List.fst_mem_of_mem_zipIdx firstMember
  have secondRouteMember : second ∈ drawing.edgeRoutes :=
    List.fst_mem_of_mem_zipIdx secondMember
  apply routesAvoidInteriorContacts_of_mem
  · intro firstSegment firstSegmentMember
      translatedSecondSegment translatedSecondSegmentMember meet
    rw [gridPolylineSegments_map_add] at translatedSecondSegmentMember
    rcases List.mem_map.mp translatedSecondSegmentMember with
      ⟨secondSegment, secondSegmentMember, rfl⟩
    rcases exists_indexedSegment_of_routeSegment_mem
        firstMember firstSegmentMember with
      ⟨firstIndexed, firstIndexedEq, firstIndexedMember⟩
    rcases exists_indexedSegment_of_routeSegment_mem
        secondMember secondSegmentMember with
      ⟨secondIndexed, secondIndexedEq, secondIndexedMember⟩
    have translatedMeet :
        GridSegment.InteriorsMeet
          (secondIndexed.segment.translate
            (drawing.periodTranslation relativeTranslate))
          (firstIndexed.segment.translate
            (drawing.periodTranslation (0, 0))) := by
      rw [firstIndexedEq, secondIndexedEq]
      simpa [offset, GridSegment.translate, periodTranslation,
        Cell.scale, Cell.add] using
        (GridSegment.interiorsMeet_comm firstSegment
          (secondSegment.translate offset)).mp meet
    have relativeInside :=
      relativeTranslate_isDoubleNeighbor_of_interiorsMeet
        endpointBounds secondIndexedMember firstIndexedMember
        translatedMeet
    apply relativeOutside
    simpa [Cell.sub] using relativeInside
  · intro firstPoint firstPointMember
      translatedSecondSegment translatedSecondSegmentMember contains
    rw [gridPolylineSegments_map_add] at translatedSecondSegmentMember
    rcases List.mem_map.mp translatedSecondSegmentMember with
      ⟨secondSegment, secondSegmentMember, rfl⟩
    rcases exists_indexedSegment_of_routeSegment_mem
        secondMember secondSegmentMember with
      ⟨secondIndexed, secondIndexedEq, secondIndexedMember⟩
    have translatedContains :
        (secondIndexed.segment.translate
          (drawing.periodTranslation relativeTranslate)).InteriorContains
          (Cell.add firstPoint
            (drawing.periodTranslation (0, 0))) := by
      rw [secondIndexedEq]
      simpa [offset, GridSegment.translate, periodTranslation,
        Cell.scale, Cell.add] using contains
    have relativeInside :=
      relativeTranslate_isDoubleNeighbor_of_expandedPointContact
        endpointBounds
        (pointBounds first firstRouteMember firstPoint firstPointMember)
        secondIndexedMember translatedContains
    apply relativeOutside
    simpa [Cell.sub] using relativeInside
  · intro translatedSecondPoint translatedSecondPointMember
      firstSegment firstSegmentMember contains
    rcases List.mem_map.mp translatedSecondPointMember with
      ⟨secondPoint, secondPointMember, rfl⟩
    rcases exists_indexedSegment_of_routeSegment_mem
        firstMember firstSegmentMember with
      ⟨firstIndexed, firstIndexedEq, firstIndexedMember⟩
    have translatedContains :
        (firstIndexed.segment.translate
          (drawing.periodTranslation (0, 0))).InteriorContains
          (Cell.add secondPoint
            (drawing.periodTranslation relativeTranslate)) := by
      rw [firstIndexedEq]
      simpa [offset, GridSegment.translate, periodTranslation,
        Cell.scale, Cell.add, add_comm] using contains
    have negativeInside :=
      relativeTranslate_isDoubleNeighbor_of_expandedPointContact
        endpointBounds
        (pointBounds second secondRouteMember
          secondPoint secondPointMember)
        firstIndexedMember translatedContains
    apply relativeOutside
    exact
      (sub_zero_mem_doubleNeighborTranslations_iff
        relativeTranslate).mp negativeInside

/-- For halo-bounded stored route points, the 24 nonzero finite cases prove
the complete nonzero relative lifted-route separation condition. -/
theorem nonzeroRelativeLiftedRoutesAvoidInteriorContacts_of_doubleNeighbor
    {drawing : PeriodicGridDrawing}
    (pointBounds : drawing.RoutePointsInExpandedSquare)
    (finite :
      drawing.DoubleNeighborNonzeroRelativeLiftedRoutesAvoidInteriorContacts) :
    drawing.NonzeroRelativeLiftedRoutesAvoidInteriorContacts := by
  intro first firstMember second secondMember
    relativeTranslate relativeNonzero
  by_cases relativeInside :
      relativeTranslate ∈ doubleNeighborTranslations
  · exact
      finite first firstMember second secondMember
        relativeTranslate relativeInside relativeNonzero
  · exact
      routesAvoidInteriorContacts_of_not_doubleNeighbor
        pointBounds firstMember secondMember relativeInside

end PeriodicGridDrawing
end LeanTrominoes
