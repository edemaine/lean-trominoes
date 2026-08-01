import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Joining a tail-contacting route piece

An incidence route may legally end on an endpoint of another route.  When
the incidence route is assembled from a contact-free prefix and a final
piece, ordinary endpoint-only separation is preserved exactly when every
listed contact of the final piece occurs at its tail.

This module records that asymmetric contact condition, transports it
through injective point maps, and supplies the corresponding endpoint-join
lemma.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every listed contact occurs at the tail of the first route and at one
of the advertised endpoints of the second route. -/
def RoutesMeetOnlyAtFirstTail
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondPoint ∈ second,
      firstPoint = secondPoint →
        first.getLast? = some firstPoint ∧
          RoutePointIsEndpoint second secondPoint

instance (first second : List Cell) :
    Decidable (RoutesMeetOnlyAtFirstTail first second) := by
  unfold RoutesMeetOnlyAtFirstTail
  infer_instance

/-- An injective point map preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.mapPoints
    {transform : Cell → Cell}
    (injective : Function.Injective transform)
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtFirstTail first second) :
    RoutesMeetOnlyAtFirstTail
      (first.map transform) (second.map transform) := by
  intro mappedFirst mappedFirstMember
    mappedSecond mappedSecondMember mappedEqual
  rcases List.mem_map.mp mappedFirstMember with
    ⟨firstPoint, firstMember, rfl⟩
  rcases List.mem_map.mp mappedSecondMember with
    ⟨secondPoint, secondMember, rfl⟩
  have pointsEqual : firstPoint = secondPoint :=
    injective mappedEqual
  have base :=
    contacts firstPoint firstMember
      secondPoint secondMember pointsEqual
  constructor
  · simpa using
      congrArg (Option.map transform) base.1
  · rcases base.2 with atHead | atLast
    · left
      simpa using
        congrArg (Option.map transform) atHead
    · right
      simpa using
        congrArg (Option.map transform) atLast

/-- A common translation preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.translate
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtFirstTail first second)
    (offset : Cell) :
    RoutesMeetOnlyAtFirstTail
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) :=
  contacts.mapPoints (cell_add_left_injective offset)

/-- Positive uniform scaling preserves first-tail-only listed contacts. -/
theorem RoutesMeetOnlyAtFirstTail.scalePolyline
    {first second : List Cell}
    {factor : Int}
    (factorPositive : 0 < factor)
    (contacts : RoutesMeetOnlyAtFirstTail first second) :
    RoutesMeetOnlyAtFirstTail
      (LeanTrominoes.scalePolyline factor first)
      (LeanTrominoes.scalePolyline factor second) :=
  contacts.mapPoints (Cell.scale_injective factorPositive.ne')

/-- Joining a contact-free prefix to an ordinarily separated final piece
preserves ordinary separation when every legal contact of the final piece
is at its tail. -/
theorem RoutesAvoidEachOther.join_left_of_tail_contact
    {first extra second : List Cell}
    {boundary : Cell}
    (firstAvoid :
      RoutesStrictlyAvoidEachOther first second)
    (extraAvoid :
      RoutesAvoidEachOther extra second)
    (extraContactsAtTail :
      RoutesMeetOnlyAtFirstTail extra second)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesAvoidEachOther
      (joinAtEndpoint first extra) second := by
  have joinedSegments :
      gridPolylineSegments (joinAtEndpoint first extra) =
        gridPolylineSegments first ++
          gridPolylineSegments extra :=
    gridPolylineSegments_joinAtEndpoint firstLast extraHead
  apply routesAvoidEachOther_of_mem
  · intro joinedSegment joinedMember
      secondSegment secondMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.1 joinedSegment firstMember
          secondSegment secondMember
    · exact
        extraAvoid.segmentsAvoid_of_mem
          joinedSegment extraMember
          secondSegment secondMember
  · intro joinedPoint joinedMember
      secondSegment secondMember
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        firstAvoid.2.1 joinedPoint firstMember
          secondSegment secondMember
    · exact
        extraAvoid.firstPointsAvoid_of_mem
          joinedPoint extraMember
          secondSegment secondMember
  · intro secondPoint secondMember
      joinedSegment joinedMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.2.2.1 secondPoint secondMember
          joinedSegment firstMember
    · exact
        extraAvoid.secondPointsAvoid_of_mem
          secondPoint secondMember
          joinedSegment extraMember
  · intro joinedPoint joinedMember
      secondPoint secondMember pointsEqual
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        (firstAvoid.2.2.2
          joinedPoint firstMember
          secondPoint secondMember pointsEqual).elim
    · have contacts :=
        extraContactsAtTail
          joinedPoint extraMember
          secondPoint secondMember pointsEqual
      have joinedLast :
          (joinAtEndpoint first extra).getLast? =
            some joinedPoint :=
        joinAtEndpoint_getLast?
          firstLast extraHead contacts.1
      exact ⟨Or.inr joinedLast, contacts.2⟩

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
