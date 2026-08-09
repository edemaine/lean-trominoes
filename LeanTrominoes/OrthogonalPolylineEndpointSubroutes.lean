import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Endpoint-respecting polyline subroutes

A route fragment used as a graph edge must do more than lie on its source
polyline: whenever it retains an advertised endpoint of the source, that
point must remain an advertised endpoint of the fragment.  This interface
is precisely what lets complete two-route separation pass to fragments.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- `fragment` uses only listed points and segments from `source`, and any
source endpoint retained by the fragment remains a fragment endpoint. -/
structure EndpointSubroute (fragment source : List Cell) : Prop where
  pointsSubset : ∀ point ∈ fragment, point ∈ source
  segmentsSubset : ∀ segment ∈ gridPolylineSegments fragment,
    segment ∈ gridPolylineSegments source
  endpointOfSourceEndpoint : ∀ point ∈ fragment,
    RoutePointIsEndpoint source point →
      RoutePointIsEndpoint fragment point

namespace EndpointSubroute

/-- Every route is an endpoint-respecting subroute of itself. -/
theorem refl (route : List Cell) : EndpointSubroute route route := by
  exact ⟨fun _ member => member, fun _ member => member,
    fun _ _ endpoint => endpoint⟩

/-- Injective point maps preserve endpoint-respecting subroutes. -/
theorem map
    {fragment source : List Cell}
    (subroute : EndpointSubroute fragment source)
    {transform : Cell → Cell}
    (injective : Function.Injective transform) :
    EndpointSubroute (fragment.map transform) (source.map transform) := by
  constructor
  · intro mappedPoint mappedMember
    rcases List.mem_map.mp mappedMember with
      ⟨point, pointMember, rfl⟩
    exact List.mem_map.mpr
      ⟨point, subroute.pointsSubset point pointMember, rfl⟩
  · intro mappedSegment mappedMember
    rw [gridPolylineSegments_map_points]
        at mappedMember ⊢
    rcases List.mem_map.mp mappedMember with
      ⟨segment, segmentMember, rfl⟩
    exact List.mem_map.mpr
      ⟨segment, subroute.segmentsSubset segment segmentMember, rfl⟩
  · intro mappedPoint mappedMember mappedEndpoint
    rcases List.mem_map.mp mappedMember with
      ⟨point, pointMember, rfl⟩
    have sourceEndpoint : RoutePointIsEndpoint source point := by
      rcases mappedEndpoint with mappedHead | mappedLast
      · left
        simp only [List.head?_map] at mappedHead
        rcases sourceHead : source.head? with _ | sourcePoint
        · simp [sourceHead] at mappedHead
        · rw [sourceHead] at mappedHead
          simp only [Option.map_some, Option.some.injEq] at mappedHead
          have sourcePointEq : sourcePoint = point :=
            injective mappedHead
          simpa [sourcePointEq] using sourceHead
      · right
        simp only [List.getLast?_map] at mappedLast
        rcases sourceLast : source.getLast? with _ | sourcePoint
        · simp [sourceLast] at mappedLast
        · rw [sourceLast] at mappedLast
          simp only [Option.map_some, Option.some.injEq] at mappedLast
          have sourcePointEq : sourcePoint = point :=
            injective mappedLast
          simpa [sourcePointEq] using sourceLast
    rcases subroute.endpointOfSourceEndpoint
        point pointMember sourceEndpoint with fragmentHead | fragmentLast
    · left
      simpa only [List.head?_map, fragmentHead, Option.map_some]
    · right
      simpa only [List.getLast?_map, fragmentLast, Option.map_some]

/-- Translation is the principal injective map used for periodic route
occurrences. -/
theorem translate
    {fragment source : List Cell}
    (subroute : EndpointSubroute fragment source)
    (offset : Cell) :
    EndpointSubroute
      (PeriodicOrthocrossing.translatePolyline offset fragment)
      (PeriodicOrthocrossing.translatePolyline offset source) := by
  exact subroute.map (Cell.add_left_injective offset)

end EndpointSubroute

/-- Complete continuous separation passes to endpoint-respecting fragments
of both routes. -/
theorem RoutesAvoidEachOther.endpointSubroutes
    {first second firstFragment secondFragment : List Cell}
    (avoids : RoutesAvoidEachOther first second)
    (firstSubroute : EndpointSubroute firstFragment first)
    (secondSubroute : EndpointSubroute secondFragment second) :
    RoutesAvoidEachOther firstFragment secondFragment := by
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstMember secondSegment secondMember
    exact avoids.segmentsAvoid_of_mem
      firstSegment
      (firstSubroute.segmentsSubset firstSegment firstMember)
      secondSegment
      (secondSubroute.segmentsSubset secondSegment secondMember)
  · intro firstPoint firstMember secondSegment secondMember
    exact avoids.firstPointsAvoid_of_mem
      firstPoint (firstSubroute.pointsSubset firstPoint firstMember)
      secondSegment
      (secondSubroute.segmentsSubset secondSegment secondMember)
  · intro secondPoint secondMember firstSegment firstMember
    exact avoids.secondPointsAvoid_of_mem
      secondPoint (secondSubroute.pointsSubset secondPoint secondMember)
      firstSegment
      (firstSubroute.segmentsSubset firstSegment firstMember)
  · intro firstPoint firstMember secondPoint secondMember pointsEqual
    rcases List.mem_iff_get.mp
        (firstSubroute.pointsSubset firstPoint firstMember) with
      ⟨firstIndex, firstAt⟩
    rcases List.mem_iff_get.mp
        (secondSubroute.pointsSubset secondPoint secondMember) with
      ⟨secondIndex, secondAt⟩
    have sourceEndpoints := avoids.2.2.2 firstIndex secondIndex
      (firstAt.trans (pointsEqual.trans secondAt.symm))
    rw [firstAt, secondAt] at sourceEndpoints
    exact
      ⟨firstSubroute.endpointOfSourceEndpoint
          firstPoint firstMember sourceEndpoints.1,
        secondSubroute.endpointOfSourceEndpoint
          secondPoint secondMember sourceEndpoints.2⟩

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
end LeanTrominoes
