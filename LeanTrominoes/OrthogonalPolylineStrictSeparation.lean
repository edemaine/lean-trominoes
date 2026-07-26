import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-!
# Strict separation of finite routes

`RoutesAvoidEachOther` permits a common point when it is an advertised
endpoint of both routes.  That is insufficient while recursively joining
route pieces, because a piece endpoint may become an internal point of the
assembled route.  This file introduces the stronger contact-free predicate
and proves that it composes through `joinAtEndpoint` on either side.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Complete continuous separation with no listed-point contact at all.
The membership formulation makes the predicate convenient to compose. -/
def RoutesStrictlyAvoidEachOther
    (first second : List Cell) : Prop :=
  (∀ firstSegment ∈ gridPolylineSegments first,
      ∀ secondSegment ∈ gridPolylineSegments second,
        ¬GridSegment.InteriorsMeet firstSegment secondSegment) ∧
    (∀ firstPoint ∈ first,
      ∀ secondSegment ∈ gridPolylineSegments second,
        ¬secondSegment.InteriorContains firstPoint) ∧
    (∀ secondPoint ∈ second,
      ∀ firstSegment ∈ gridPolylineSegments first,
        ¬firstSegment.InteriorContains secondPoint) ∧
    ∀ firstPoint ∈ first,
      ∀ secondPoint ∈ second,
        firstPoint ≠ secondPoint

instance (first second : List Cell) :
    Decidable (RoutesStrictlyAvoidEachOther first second) := by
  unfold RoutesStrictlyAvoidEachOther
  infer_instance

/-- Ordinary route separation plus absence of listed contacts gives strict
route separation. -/
theorem routesStrictlyAvoidEachOther_of_avoid_of_noContact
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (noContact :
      ∀ firstPoint ∈ first,
        ∀ secondPoint ∈ second,
          firstPoint ≠ secondPoint) :
    RoutesStrictlyAvoidEachOther first second := by
  unfold RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, noContact⟩
  · intro firstSegment firstMember secondSegment secondMember
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.1 firstIndex secondIndex
  · intro firstPoint firstMember secondSegment secondMember
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstIndex, firstEqual⟩
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondIndex, secondEqual⟩
    rw [← firstEqual, ← secondEqual]
    exact avoid.2.1 firstIndex secondIndex
  · intro secondPoint secondMember firstSegment firstMember
    rcases List.mem_iff_get.mp secondMember with
      ⟨secondIndex, secondEqual⟩
    rcases List.mem_iff_get.mp firstMember with
      ⟨firstIndex, firstEqual⟩
    rw [← secondEqual, ← firstEqual]
    exact avoid.2.2.1 secondIndex firstIndex

/-- Strict separation implies the ordinary endpoint-contact-permitting
predicate. -/
theorem RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesAvoidEachOther first second := by
  unfold RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    exact
      strict.1
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex)
  · intro firstIndex secondIndex
    exact
      strict.2.1
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex)
  · intro secondIndex firstIndex
    exact
      strict.2.2.1
        _ (List.get_mem _ secondIndex)
        _ (List.get_mem _ firstIndex)
  · intro firstIndex secondIndex equal
    exact
      (strict.2.2.2
        _ (List.get_mem _ firstIndex)
        _ (List.get_mem _ secondIndex)
        equal).elim

/-- Segment enumeration of `joinAtEndpoint` is exact when the advertised
boundary points agree. -/
theorem gridPolylineSegments_joinAtEndpoint
    {first second : List Cell} {boundary : Cell}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    gridPolylineSegments (joinAtEndpoint first second) =
      gridPolylineSegments first ++
        gridPolylineSegments second := by
  simpa [joinAtEndpoint,
    PeriodicOrthocrossing.joinPolylines] using
    gridPolylineSegments_joinPolylines firstLast secondHead

/-- Joining two pieces on the left preserves strict separation from a
third route when both pieces are strictly separated from it. -/
theorem RoutesStrictlyAvoidEachOther.join_left
    {first extra second : List Cell} {boundary : Cell}
    (firstAvoid : RoutesStrictlyAvoidEachOther first second)
    (extraAvoid : RoutesStrictlyAvoidEachOther extra second)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint first extra) second := by
  have segments :
      gridPolylineSegments (joinAtEndpoint first extra) =
        gridPolylineSegments first ++
          gridPolylineSegments extra :=
    gridPolylineSegments_joinAtEndpoint firstLast extraHead
  unfold RoutesStrictlyAvoidEachOther at firstAvoid extraAvoid ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro joinedSegment joinedMember secondSegment secondMember
    rw [segments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.1 joinedSegment firstMember
          secondSegment secondMember
    · exact
        extraAvoid.1 joinedSegment extraMember
          secondSegment secondMember
  · intro joinedPoint joinedMember secondSegment secondMember
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        firstAvoid.2.1 joinedPoint firstMember
          secondSegment secondMember
    · exact
        extraAvoid.2.1 joinedPoint extraMember
          secondSegment secondMember
  · intro secondPoint secondMember joinedSegment joinedMember
    rw [segments, List.mem_append] at joinedMember
    rcases joinedMember with firstMember | extraMember
    · exact
        firstAvoid.2.2.1 secondPoint secondMember
          joinedSegment firstMember
    · exact
        extraAvoid.2.2.1 secondPoint secondMember
          joinedSegment extraMember
  · intro joinedPoint joinedMember secondPoint secondMember
    rcases mem_joinAtEndpoint joinedMember with
      firstMember | extraMember
    · exact
        firstAvoid.2.2.2 joinedPoint firstMember
          secondPoint secondMember
    · exact
        extraAvoid.2.2.2 joinedPoint extraMember
          secondPoint secondMember

/-- Joining two pieces on the right preserves strict separation from a
first route when it is strictly separated from both pieces. -/
theorem RoutesStrictlyAvoidEachOther.join_right
    {first second extra : List Cell} {boundary : Cell}
    (secondAvoid : RoutesStrictlyAvoidEachOther first second)
    (extraAvoid : RoutesStrictlyAvoidEachOther first extra)
    (secondLast : second.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesStrictlyAvoidEachOther
      first (joinAtEndpoint second extra) := by
  have segments :
      gridPolylineSegments (joinAtEndpoint second extra) =
        gridPolylineSegments second ++
          gridPolylineSegments extra :=
    gridPolylineSegments_joinAtEndpoint secondLast extraHead
  unfold RoutesStrictlyAvoidEachOther at secondAvoid extraAvoid ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember joinedSegment joinedMember
    rw [segments, List.mem_append] at joinedMember
    rcases joinedMember with secondMember | extraMember
    · exact
        secondAvoid.1 firstSegment firstMember
          joinedSegment secondMember
    · exact
        extraAvoid.1 firstSegment firstMember
          joinedSegment extraMember
  · intro firstPoint firstMember joinedSegment joinedMember
    rw [segments, List.mem_append] at joinedMember
    rcases joinedMember with secondMember | extraMember
    · exact
        secondAvoid.2.1 firstPoint firstMember
          joinedSegment secondMember
    · exact
        extraAvoid.2.1 firstPoint firstMember
          joinedSegment extraMember
  · intro joinedPoint joinedMember firstSegment firstMember
    rcases mem_joinAtEndpoint joinedMember with
      secondMember | extraMember
    · exact
        secondAvoid.2.2.1 joinedPoint secondMember
          firstSegment firstMember
    · exact
        extraAvoid.2.2.1 joinedPoint extraMember
          firstSegment firstMember
  · intro firstPoint firstMember joinedPoint joinedMember
    rcases mem_joinAtEndpoint joinedMember with
      secondMember | extraMember
    · exact
        secondAvoid.2.2.2 firstPoint firstMember
          joinedPoint secondMember
    · exact
        extraAvoid.2.2.2 firstPoint firstMember
          joinedPoint extraMember

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
