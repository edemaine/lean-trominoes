import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicGridDrawingScaling
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

/-- Ordinary endpoint-only route separation becomes contact-free when none
of the two advertised endpoints of the first route equals either advertised
endpoint of the second route. -/
theorem routesStrictlyAvoidEachOther_of_avoid_of_endpoints_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (headHeadNe : first.head? ≠ second.head?)
    (headLastNe : first.head? ≠ second.getLast?)
    (lastHeadNe : first.getLast? ≠ second.head?)
    (lastLastNe : first.getLast? ≠ second.getLast?) :
    RoutesStrictlyAvoidEachOther first second := by
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact avoid
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstPointEqual⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondPointEqual⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstPointEqual.trans
      (pointsEqual.trans secondPointEqual.symm)
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstPointEqual, secondPointEqual] at endpoints
  rcases endpoints.1 with firstHead | firstLast <;>
    rcases endpoints.2 with secondHead | secondLast
  · exact
      headHeadNe
        (firstHead.trans
          ((congrArg some pointsEqual).trans secondHead.symm))
  · exact
      headLastNe
        (firstHead.trans
          ((congrArg some pointsEqual).trans secondLast.symm))
  · exact
      lastHeadNe
        (firstLast.trans
          ((congrArg some pointsEqual).trans secondHead.symm))
  · exact
      lastLastNe
        (firstLast.trans
          ((congrArg some pointsEqual).trans secondLast.symm))

/-- Restricting the first route to one of its listed points preserves
ordinary route separation.  The resulting singleton has no segments. -/
theorem RoutesAvoidEachOther.singleton_left
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    {point : Cell}
    (pointMember : point ∈ first) :
    RoutesAvoidEachOther [point] second := by
  rcases List.mem_iff_get.mp pointMember with
    ⟨sourceIndex, sourceEquation⟩
  unfold RoutesAvoidEachOther
    SegmentInteriorsDisjoint
    RoutePointsAvoidInteriors
    RoutesMeetOnlyAtEndpoints
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro singletonSegment
    exact Fin.elim0 singletonSegment
  · intro singletonPoint secondSegment
    have singletonEquation :
        [point].get singletonPoint = point := by
      simp
    rw [singletonEquation, ← sourceEquation]
    exact avoid.2.1 sourceIndex secondSegment
  · intro _secondPoint singletonSegment
    exact Fin.elim0 singletonSegment
  · intro singletonPoint secondPoint equal
    have singletonEquation :
        [point].get singletonPoint = point := by
      simp
    have sourceEqual :
        first.get sourceIndex = second.get secondPoint := by
      exact
        sourceEquation.trans
          (singletonEquation.symm.trans equal)
    have endpoints :=
      avoid.2.2.2 sourceIndex secondPoint sourceEqual
    constructor
    · simp [RoutePointIsEndpoint]
    · exact endpoints.2

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

/-- Restricting the first route to one of its listed points preserves
strict separation. -/
theorem RoutesStrictlyAvoidEachOther.singleton_left
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    {point : Cell}
    (pointMember : point ∈ first) :
    RoutesStrictlyAvoidEachOther [point] second := by
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact
    (strict.toRoutesAvoidEachOther.singleton_left pointMember)
  intro firstPoint firstMember secondPoint secondMember
  simp only [List.mem_singleton] at firstMember
  subst firstPoint
  exact strict.2.2.2 point pointMember
    secondPoint secondMember

/-- Contact-free route separation is symmetric. -/
theorem RoutesStrictlyAvoidEachOther.symm
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther second first := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  exact
    ⟨fun secondSegment secondMember firstSegment firstMember =>
        by
          intro meet
          apply strict.1 firstSegment firstMember
            secondSegment secondMember
          simpa [GridSegment.InteriorsMeet,
            GridSegment.OpenIntervalsOverlap,
            and_comm, and_left_comm, and_assoc,
            or_comm, or_left_comm, or_assoc,
            eq_comm] using meet,
      strict.2.2.1,
      strict.2.1,
      fun secondPoint secondMember firstPoint firstMember equal =>
        strict.2.2.2 firstPoint firstMember
          secondPoint secondMember equal.symm⟩

/-- Restricting the second route to one of its listed points preserves
strict separation. -/
theorem RoutesStrictlyAvoidEachOther.singleton_right
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    {point : Cell}
    (pointMember : point ∈ second) :
    RoutesStrictlyAvoidEachOther first [point] :=
  strict.symm.singleton_left pointMember |>.symm

/-- Common pointwise translation preserves contact-free continuous route
separation. -/
theorem RoutesStrictlyAvoidEachOther.translatePolyline
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (offset : Cell) :
    RoutesStrictlyAvoidEachOther
      (PeriodicOrthocrossing.translatePolyline offset first)
      (PeriodicOrthocrossing.translatePolyline offset second) := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  rw [gridPolylineSegments_translatePolyline,
    gridPolylineSegments_translatePolyline]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember meet
    rcases List.mem_map.mp firstMember with
      ⟨sourceFirst, sourceFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSecond, sourceSecondMember, rfl⟩
    apply strict.1 sourceFirst sourceFirstMember
      sourceSecond sourceSecondMember
    exact
      (GridSegment.interiorsMeet_translate_both_iff
        sourceFirst sourceSecond offset).mp meet
  · intro firstPoint firstMember secondSegment secondMember contains
    unfold PeriodicOrthocrossing.translatePolyline at firstMember
    rcases List.mem_map.mp firstMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    apply strict.2.1 sourcePoint sourcePointMember
      sourceSegment sourceSegmentMember
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        sourceSegment offset sourcePoint).mp
        (by simpa [Cell.add, add_comm] using contains)
  · intro secondPoint secondMember firstSegment firstMember contains
    unfold PeriodicOrthocrossing.translatePolyline at secondMember
    rcases List.mem_map.mp secondMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rcases List.mem_map.mp firstMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    apply strict.2.2.1 sourcePoint sourcePointMember
      sourceSegment sourceSegmentMember
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        sourceSegment offset sourcePoint).mp
        (by simpa [Cell.add, add_comm] using contains)
  · intro firstPoint firstMember secondPoint secondMember equal
    unfold PeriodicOrthocrossing.translatePolyline at firstMember secondMember
    rcases List.mem_map.mp firstMember with
      ⟨sourceFirst, sourceFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSecond, sourceSecondMember, rfl⟩
    exact strict.2.2.2 sourceFirst sourceFirstMember
      sourceSecond sourceSecondMember
      (Cell.add_left_injective offset equal)

/-- Positive uniform scaling preserves contact-free route separation. -/
theorem RoutesStrictlyAvoidEachOther.scalePolyline
    {first second : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther
      (LeanTrominoes.scalePolyline factor first)
      (LeanTrominoes.scalePolyline factor second) := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  rw [gridPolylineSegments_scalePolyline,
    gridPolylineSegments_scalePolyline]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    intro meet
    exact
      strict.1 originalFirst originalFirstMember
        originalSecond originalSecondMember
        ((GridSegment.interiorsMeet_scale_iff
          factorPositive originalFirst originalSecond).mp meet)
  · intro firstPoint firstMember secondSegment secondMember
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    intro contains
    exact
      strict.2.1 originalFirst originalFirstMember
        originalSecond originalSecondMember
        ((GridSegment.interiorContains_scale_iff
          factorPositive originalSecond originalFirst).mp contains)
  · intro secondPoint secondMember firstSegment firstMember
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    intro contains
    exact
      strict.2.2.1 originalSecond originalSecondMember
        originalFirst originalFirstMember
        ((GridSegment.interiorContains_scale_iff
          factorPositive originalFirst originalSecond).mp contains)
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases List.mem_map.mp firstMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨originalSecond, originalSecondMember, rfl⟩
    exact
      strict.2.2.2 originalFirst originalFirstMember
        originalSecond originalSecondMember
        (Cell.scale_injective factorPositive.ne' equal)

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
