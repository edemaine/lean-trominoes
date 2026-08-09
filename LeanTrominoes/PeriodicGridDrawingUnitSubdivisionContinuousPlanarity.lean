import LeanTrominoes.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.PeriodicGridDrawingNoImmediateReversal

/-!
# Continuous planarity under unit subdivision

Unit subdivision does not change the geometric support of an orthogonal
route.  This module strengthens the basic unit-subdivision interface by
showing that it also preserves disjoint open segment interiors, including
for two segments belonging to the same stored route occurrence.
-/

namespace LeanTrominoes

set_option maxHeartbeats 800000

namespace AxisDirection

/-- Pointwise segment form of a binary chain relation. -/
private theorem isChain_iff_segments
    (relation : Cell → Cell → Prop) (points : List Cell) :
    points.IsChain relation ↔
      ∀ segment ∈ gridPolylineSegments points,
        relation segment.start segment.finish := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      constructor
      · intro chain segment segmentMember
        have parts := List.isChain_cons_cons.mp chain
        simp only [gridPolylineSegments,
          List.mem_cons] at segmentMember
        rcases segmentMember with rfl | segmentMember
        · exact parts.1
        · exact (tailInduction second).mp parts.2 _ segmentMember
      · intro segments
        apply List.isChain_cons_cons.mpr
        constructor
        · exact segments (GridSegment.mk first second)
            (by simp [gridPolylineSegments])
        · apply (tailInduction second).mpr
          intro segment segmentMember
          exact segments segment
            (by
              simp only [gridPolylineSegments, List.mem_cons]
              exact Or.inr segmentMember)

/-- Unit segments with the same directed axis can have meeting interiors
only when they are the same directed segment. -/
private theorem unitAxisSteps_eq_of_sameDirection_of_interiorsMeet
    {firstStart firstFinish secondStart secondFinish : Cell}
    (firstUnit : IsUnitAxisStep firstStart firstFinish)
    (secondUnit : IsUnitAxisStep secondStart secondFinish)
    (sameDirection :
      between firstStart firstFinish =
        between secondStart secondFinish)
    (meet :
      GridSegment.InteriorsMeet
        (GridSegment.mk firstStart firstFinish)
        (GridSegment.mk secondStart secondFinish)) :
    GridSegment.mk firstStart firstFinish =
      GridSegment.mk secondStart secondFinish := by
  rcases firstUnit with ⟨firstDirection, firstGenuine, rfl⟩
  rcases secondUnit with ⟨secondDirection, secondGenuine, rfl⟩
  have directionsEqual : firstDirection = secondDirection := by
    simpa [between_add_step _ firstGenuine,
      between_add_step _ secondGenuine] using sameDirection
  subst secondDirection
  rcases firstStart with ⟨firstX, firstY⟩
  rcases secondStart with ⟨secondX, secondY⟩
  cases firstDirection <;>
    simp_all [IsGenuine, step, Cell.add,
      GridSegment.InteriorsMeet,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween] <;>
    omega

/-- The consecutive unit segments generated inside one source segment have
pairwise disjoint relative interiors. -/
private theorem unitSegmentPoints_segments_pairwise
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (gridPolylineSegments (unitSegmentPoints first second)).Pairwise
      (fun firstSegment secondSegment =>
        ¬GridSegment.InteriorsMeet firstSegment secondSegment) := by
  rw [List.pairwise_iff_get]
  intro firstIndex secondIndex indicesOrdered
  have unitSteps := unitSegmentPoints_unitSteps aligned
  have segmentUnits :=
    (unitSteps_iff_segments
      (unitSegmentPoints first second)).mp unitSteps
  have directions := unitSegmentPoints_direction aligned
  have segmentDirections :=
    (isChain_iff_segments
      (fun source target => between source target = between first second)
      (unitSegmentPoints first second)).mp directions
  intro meet
  have segmentsEqual :=
    unitAxisSteps_eq_of_sameDirection_of_interiorsMeet
      (segmentUnits _ (List.get_mem _ firstIndex))
      (segmentUnits _ (List.get_mem _ secondIndex))
      (by
        exact
          (segmentDirections _ (List.get_mem _ firstIndex)).trans
            (segmentDirections _ (List.get_mem _ secondIndex)).symm)
      meet
  have segmentsNodup :
      (gridPolylineSegments
        (unitSegmentPoints first second)).Nodup :=
    gridPolylineSegments_nodup_of_points_nodup
      (unitSegmentPoints_nodup aligned)
  have indicesEqual : firstIndex = secondIndex :=
    (List.nodup_iff_injective_get.mp segmentsNodup) segmentsEqual
  exact (ne_of_lt indicesOrdered) indicesEqual

/-- Pairwise source-segment separation survives ordered unit subdivision of
one orthogonal route. -/
theorem unitSubdividePolyline_segments_pairwise
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points)
    (disjoint : RouteSegmentsHaveDisjointInteriors points) :
    (gridPolylineSegments (unitSubdividePolyline points)).Pairwise
      (fun firstSegment secondSegment =>
        ¬GridSegment.InteriorsMeet firstSegment secondSegment) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [unitSubdividePolyline, gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      have firstLast :
          (unitSegmentPoints first second).getLast? = some second :=
        unitSegmentPoints_getLast? orthogonalParts.1
      have tailHead :
          (unitSubdividePolyline (second :: rest)).head? = some second := by
        simpa using unitSubdividePolyline_head?
          (points := second :: rest) (by simp)
      rw [unitSubdividePolyline,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_joinAtEndpoint
          firstLast tailHead,
        List.pairwise_append]
      refine ⟨unitSegmentPoints_segments_pairwise orthogonalParts.1,
        tailInduction second orthogonalParts.2 disjoint.tail, ?_⟩
      intro firstChild firstChildMember secondChild secondChildMember
      have firstEndpoints :=
        gridPolylineSegments_endpoints_mem firstChildMember
      have firstStartContained :=
        unitSegmentPoints_mem_parent orthogonalParts.1 firstEndpoints.1
      have firstFinishContained :=
        unitSegmentPoints_mem_parent orthogonalParts.1 firstEndpoints.2
      rcases
          unitSubdividePolyline_segment_provenance
            orthogonalParts.2 secondChildMember with
        ⟨secondParent, secondParentMember,
          secondStartContained, secondFinishContained⟩
      rcases List.mem_iff_get.mp secondParentMember with
        ⟨secondParentIndex, secondParentEquation⟩
      let firstSourceIndex :
          Fin (gridPolylineSegments
            (first :: second :: rest)).length :=
        ⟨0, by simp [gridPolylineSegments]⟩
      let secondSourceIndex :
          Fin (gridPolylineSegments
            (first :: second :: rest)).length :=
        ⟨secondParentIndex.val + 1, by
          simpa [gridPolylineSegments] using
            Nat.add_lt_add_right secondParentIndex.isLt 1⟩
      have sourceIndicesDifferent :
          firstSourceIndex ≠ secondSourceIndex := by
        intro equal
        have := congrArg Fin.val equal
        simp [firstSourceIndex, secondSourceIndex] at this
      have parentsAvoid :=
        disjoint firstSourceIndex secondSourceIndex sourceIndicesDifferent
      intro childrenMeet
      apply parentsAvoid
      have parentMeet :=
        GridSegment.interiorsMeet_of_interiorsMeet_of_endpointsContained
          orthogonalParts.1
          ((PeriodicOrthocrossing.orthogonalPolyline_iff_segments
            (second :: rest)).mp orthogonalParts.2
              secondParent secondParentMember)
          firstStartContained firstFinishContained
          secondStartContained secondFinishContained childrenMeet
      change
        (GridSegment.mk first second).InteriorsMeet
          ((gridPolylineSegments (second :: rest)).get
            secondParentIndex)
      rw [secondParentEquation]
      exact parentMeet

/-- Fin-indexed form of pairwise separation for a unit-subdivided route. -/
theorem unitSubdividePolyline_routeSegmentsHaveDisjointInteriors
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points)
    (disjoint : RouteSegmentsHaveDisjointInteriors points) :
    RouteSegmentsHaveDisjointInteriors
      (unitSubdividePolyline points) := by
  intro firstIndex secondIndex indicesDifferent
  have pairwise :=
    unitSubdividePolyline_segments_pairwise orthogonal disjoint
  rcases lt_or_gt_of_ne indicesDifferent with ordered | ordered
  · exact pairwise.rel_get_of_lt ordered
  · intro meet
    exact pairwise.rel_get_of_lt ordered
      ((GridSegment.interiorsMeet_comm _ _).mpr meet)

end AxisDirection

namespace PeriodicGridDrawing

private theorem tagged_eq_of_mem_zipIdx_of_snd_eq
    {Item : Type*} {items : List Item}
    {first second : Item × Nat}
    (firstMember : first ∈ items.zipIdx)
    (secondMember : second ∈ items.zipIdx)
    (indicesEqual : first.2 = second.2) :
    first = second := by
  apply Prod.ext
  · have firstAt := (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondAt := (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [indicesEqual, secondAt] at firstAt
    exact Option.some.inj firstAt.symm
  · exact indicesEqual

private theorem segmentOccurrenceKey_ne_of_routeOccurrence_ne
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

private theorem orthogonalPolyline_of_route_mem
    {drawing : PeriodicGridDrawing}
    (orthogonal : drawing.IsOrthogonal)
    {taggedRoute : List Cell × Nat}
    (routeMember : taggedRoute ∈ drawing.edgeRoutes.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline taggedRoute.1 := by
  rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
  intro segment segmentMember
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEquation⟩
  let indexed : IndexedGridSegment :=
    ⟨taggedRoute.2, segmentIndex,
      (gridPolylineSegments taggedRoute.1).get segmentIndex⟩
  have aligned := orthogonal indexed
    (indexedSegment_mem_of_route_mem routeMember segmentIndex)
  change
    ((gridPolylineSegments taggedRoute.1).get
      segmentIndex).IsAxisAligned at aligned
  rw [segmentEquation] at aligned
  exact aligned

/-- Unit subdivision preserves continuous relative-interior separation in
the full infinite periodic lift. -/
theorem routesHaveDisjointInteriors_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (continuous : drawing.IsContinuouslyPlanar)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent
  unfold indexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases List.mem_map.mp firstSegmentMember with
    ⟨firstSegment, firstSegmentMember, firstEqual⟩
  have firstSegmentTaggedMember :
      firstSegment ∈ (gridPolylineSegments firstRoute.1).zipIdx :=
    firstSegmentMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  rcases List.mem_map.mp secondSegmentMember with
    ⟨secondSegment, secondSegmentMember, secondEqual⟩
  have secondSegmentTaggedMember :
      secondSegment ∈ (gridPolylineSegments secondRoute.1).zipIdx :=
    secondSegmentMember
  subst second
  rw [unitSubdivide, List.zipIdx_map] at firstRouteMember secondRouteMember
  rcases List.mem_map.mp firstRouteMember with
    ⟨firstSourceRoute, firstSourceRouteMember,
      firstRouteEqual⟩
  rcases List.mem_map.mp secondRouteMember with
    ⟨secondSourceRoute, secondSourceRouteMember,
      secondRouteEqual⟩
  have firstRouteValueEqual :
      firstRoute.1 =
        AxisDirection.unitSubdividePolyline firstSourceRoute.1 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.fst firstRouteEqual).symm
  have firstRouteIndexEqual : firstRoute.2 = firstSourceRoute.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd firstRouteEqual).symm
  have secondRouteValueEqual :
      secondRoute.1 =
        AxisDirection.unitSubdividePolyline secondSourceRoute.1 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.fst secondRouteEqual).symm
  have secondRouteIndexEqual : secondRoute.2 = secondSourceRoute.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd secondRouteEqual).symm
  rw [firstRouteValueEqual] at firstSegmentTaggedMember
  rw [secondRouteValueEqual] at secondSegmentTaggedMember
  by_cases occurrencesDifferent :
      (firstSourceRoute.2, firstTranslate) ≠
        (secondSourceRoute.2, secondTranslate)
  · rcases
        AxisDirection.unitSubdividePolyline_segment_provenance
          (orthogonalPolyline_of_route_mem
            orthogonal firstSourceRouteMember)
          (List.fst_mem_of_mem_zipIdx firstSegmentTaggedMember) with
      ⟨firstParent, firstParentMember,
        firstStartContained, firstFinishContained⟩
    rcases
        AxisDirection.unitSubdividePolyline_segment_provenance
          (orthogonalPolyline_of_route_mem
            orthogonal secondSourceRouteMember)
          (List.fst_mem_of_mem_zipIdx secondSegmentTaggedMember) with
      ⟨secondParent, secondParentMember,
        secondStartContained, secondFinishContained⟩
    rcases List.mem_iff_get.mp firstParentMember with
      ⟨firstParentIndex, firstParentEquation⟩
    rcases List.mem_iff_get.mp secondParentMember with
      ⟨secondParentIndex, secondParentEquation⟩
    let firstIndexed : IndexedGridSegment :=
      ⟨firstSourceRoute.2, firstParentIndex,
        (gridPolylineSegments firstSourceRoute.1).get firstParentIndex⟩
    let secondIndexed : IndexedGridSegment :=
      ⟨secondSourceRoute.2, secondParentIndex,
        (gridPolylineSegments secondSourceRoute.1).get secondParentIndex⟩
    have firstIndexedMember : firstIndexed ∈ drawing.indexedSegments := by
      exact indexedSegment_mem_of_route_mem
        firstSourceRouteMember firstParentIndex
    have secondIndexedMember : secondIndexed ∈ drawing.indexedSegments := by
      exact indexedSegment_mem_of_route_mem
        secondSourceRouteMember secondParentIndex
    have sourceKeysDifferent :
        SegmentOccurrenceKey firstIndexed firstTranslate ≠
          SegmentOccurrenceKey secondIndexed secondTranslate :=
      segmentOccurrenceKey_ne_of_routeOccurrence_ne occurrencesDifferent
    have parentsAvoid :=
      continuous.noInteriorsMeet
        firstIndexedMember secondIndexedMember sourceKeysDifferent
    intro childrenMeet
    apply parentsAvoid
    have parentMeet :=
      GridSegment.interiorsMeet_of_interiorsMeet_of_endpointsContained
        (firstParent := firstParent.translate
          (drawing.periodTranslation firstTranslate))
        (secondParent := secondParent.translate
          (drawing.periodTranslation secondTranslate))
        (firstChild := firstSegment.1.translate
          (drawing.periodTranslation firstTranslate))
        (secondChild := secondSegment.1.translate
          (drawing.periodTranslation secondTranslate))
        ((GridSegment.isAxisAligned_translate firstParent
          (drawing.periodTranslation firstTranslate)).mpr
          ((PeriodicOrthocrossing.orthogonalPolyline_iff_segments
            firstSourceRoute.1).mp
              (orthogonalPolyline_of_route_mem
                orthogonal firstSourceRouteMember)
              firstParent firstParentMember))
        ((GridSegment.isAxisAligned_translate secondParent
          (drawing.periodTranslation secondTranslate)).mpr
          ((PeriodicOrthocrossing.orthogonalPolyline_iff_segments
            secondSourceRoute.1).mp
              (orthogonalPolyline_of_route_mem
                orthogonal secondSourceRouteMember)
              secondParent secondParentMember))
        (by
          simpa [GridSegment.translate, Cell.add, add_comm] using
            (contains_translate_iff firstParent
              (drawing.periodTranslation firstTranslate)
              firstSegment.1.start).mpr firstStartContained)
        (by
          simpa [GridSegment.translate, Cell.add, add_comm] using
            (contains_translate_iff firstParent
              (drawing.periodTranslation firstTranslate)
              firstSegment.1.finish).mpr firstFinishContained)
        (by
          simpa [GridSegment.translate, Cell.add, add_comm] using
            (contains_translate_iff secondParent
              (drawing.periodTranslation secondTranslate)
              secondSegment.1.start).mpr secondStartContained)
        (by
          simpa [GridSegment.translate, Cell.add, add_comm] using
            (contains_translate_iff secondParent
              (drawing.periodTranslation secondTranslate)
              secondSegment.1.finish).mpr secondFinishContained)
        (by simpa [firstRouteIndexEqual, secondRouteIndexEqual] using childrenMeet)
    change
      (GridSegment.translate
        (drawing.periodTranslation firstTranslate)
        ((gridPolylineSegments firstSourceRoute.1).get
          firstParentIndex)).InteriorsMeet
        (GridSegment.translate
          (drawing.periodTranslation secondTranslate)
          ((gridPolylineSegments secondSourceRoute.1).get
            secondParentIndex))
    rw [firstParentEquation, secondParentEquation]
    exact parentMeet
  · have occurrenceEqual :
        (firstSourceRoute.2, firstTranslate) =
          (secondSourceRoute.2, secondTranslate) :=
      not_ne_iff.mp occurrencesDifferent
    have sourceRouteEqual : firstSourceRoute = secondSourceRoute :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstSourceRouteMember secondSourceRouteMember
        (congrArg Prod.fst occurrenceEqual)
    subst secondSourceRoute
    have translatesEqual : firstTranslate = secondTranslate :=
      congrArg Prod.snd occurrenceEqual
    subst secondTranslate
    have segmentIndicesDifferent : firstSegment.2 ≠ secondSegment.2 := by
      intro indicesEqual
      apply keysDifferent
      simp [SegmentOccurrenceKey, firstRouteIndexEqual,
        secondRouteIndexEqual, indicesEqual]
    have routeIndexLt :
        firstSourceRoute.2 < drawing.edgeRoutes.length :=
      List.snd_lt_of_mem_zipIdx firstSourceRouteMember
    have sourceRouteAt :
        drawing.edgeRoutes[firstSourceRoute.2] = firstSourceRoute.1 := by
      have lookup :=
        (List.mem_zipIdx_iff_getElem?).mp firstSourceRouteMember
      exact (List.getElem?_eq_some_iff.mp lookup).2
    have sourceDisjoint :=
      continuous.routeSegmentsHaveDisjointInteriors routeIndexLt
    rw [sourceRouteAt] at sourceDisjoint
    have sourceOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline firstSourceRoute.1 :=
      orthogonalPolyline_of_route_mem orthogonal firstSourceRouteMember
    have subdividedDisjoint :=
      AxisDirection.unitSubdividePolyline_routeSegmentsHaveDisjointInteriors
        sourceOrthogonal sourceDisjoint
    let firstIndex :
        Fin (gridPolylineSegments
          (AxisDirection.unitSubdividePolyline
            firstSourceRoute.1)).length :=
      ⟨firstSegment.2,
        List.snd_lt_of_mem_zipIdx firstSegmentTaggedMember⟩
    let secondIndex :
        Fin (gridPolylineSegments
          (AxisDirection.unitSubdividePolyline
            firstSourceRoute.1)).length :=
      ⟨secondSegment.2,
        List.snd_lt_of_mem_zipIdx secondSegmentTaggedMember⟩
    have localAvoid :=
      subdividedDisjoint firstIndex secondIndex
        (by
          intro equal
          apply segmentIndicesDifferent
          exact congrArg Fin.val equal)
    intro translatedMeet
    apply localAvoid
    have baseMeet :=
      (GridSegment.interiorsMeet_translate_both_iff
        firstSegment.1 secondSegment.1
        (drawing.periodTranslation firstTranslate)).mp
        (by simpa using translatedMeet)
    have firstAt :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstSegmentTaggedMember)).2
    have secondAt :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondSegmentTaggedMember)).2
    simpa [firstIndex, secondIndex, firstAt, secondAt] using baseMeet

/-- Orthogonal continuous drawings remain continuously planar after every
stored route is replaced by its ordered unit subdivision. -/
theorem isContinuouslyPlanar_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (continuous : drawing.IsContinuouslyPlanar)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.IsContinuouslyPlanar :=
  ⟨isPlanar_unitSubdivide drawing orthogonal,
    routesHaveDisjointInteriors_unitSubdivide
      drawing continuous orthogonal⟩

end PeriodicGridDrawing

end LeanTrominoes
