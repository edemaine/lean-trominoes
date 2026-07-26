import LeanTrominoes.OrthogonalPolylineUnitSubdivision
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Continuous planarity excludes immediate route reversals

If an orthogonal polyline immediately reverses direction at a listed point,
the two adjacent segment interiors overlap on a nonempty interval.  This
file packages that local fact and then applies a periodic drawing's
continuous-planarity certificate to every stored route.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- The four direction constructors are characterized by their coordinate
equalities and strict inequalities. -/
theorem between_eq_east_iff (first second : Cell) :
    between first second = .east ↔
      first.2 = second.2 ∧ first.1 < second.1 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

theorem between_eq_north_iff (first second : Cell) :
    between first second = .north ↔
      first.1 = second.1 ∧ first.2 < second.2 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

theorem between_eq_west_iff (first second : Cell) :
    between first second = .west ↔
      first.2 = second.2 ∧ second.1 < first.1 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

theorem between_eq_south_iff (first second : Cell) :
    between first second = .south ↔
      first.1 = second.1 ∧ second.2 < first.2 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

/-- Reversing immediately after a genuine orthogonal segment forces the two
adjacent open segment interiors to overlap. -/
theorem interiorsMeet_of_immediateReversal
    {first center next : Cell}
    (incomingGenuine :
      (between first center).IsGenuine)
    (reversal :
      between center next =
        (between first center).opposite) :
    GridSegment.InteriorsMeet
      (GridSegment.mk first center)
      (GridSegment.mk center next) := by
  cases incoming : between first center with
  | east =>
      have firstData :=
        (between_eq_east_iff first center).mp incoming
      have nextData :=
        (between_eq_west_iff center next).mp (by
          simpa [incoming, opposite] using reversal)
      rcases first with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      rcases next with ⟨nextX, nextY⟩
      rcases firstData with ⟨firstYEq, firstXLt⟩
      rcases nextData with ⟨nextYEq, nextXLt⟩
      change firstY = centerY at firstYEq
      change firstX < centerX at firstXLt
      change centerY = nextY at nextYEq
      change nextX < centerX at nextXLt
      apply Or.inl
      simp [GridSegment.IsHorizontal,
        GridSegment.OpenIntervalsOverlap,
        firstYEq, nextYEq,
        min_eq_left firstXLt.le,
        max_eq_right firstXLt.le,
        min_eq_right nextXLt.le,
        max_eq_left nextXLt.le,
        firstXLt, nextXLt]
      constructor <;> omega
  | north =>
      have firstData :=
        (between_eq_north_iff first center).mp incoming
      have nextData :=
        (between_eq_south_iff center next).mp (by
          simpa [incoming, opposite] using reversal)
      rcases first with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      rcases next with ⟨nextX, nextY⟩
      rcases firstData with ⟨firstXEq, firstYLt⟩
      rcases nextData with ⟨nextXEq, nextYLt⟩
      change firstX = centerX at firstXEq
      change firstY < centerY at firstYLt
      change centerX = nextX at nextXEq
      change nextY < centerY at nextYLt
      apply Or.inr
      apply Or.inl
      simp [GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap,
        firstXEq, nextXEq,
        min_eq_left firstYLt.le,
        max_eq_right firstYLt.le,
        min_eq_right nextYLt.le,
        max_eq_left nextYLt.le,
        firstYLt, nextYLt]
      constructor <;> omega
  | west =>
      have firstData :=
        (between_eq_west_iff first center).mp incoming
      have nextData :=
        (between_eq_east_iff center next).mp (by
          simpa [incoming, opposite] using reversal)
      rcases first with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      rcases next with ⟨nextX, nextY⟩
      rcases firstData with ⟨firstYEq, firstXLt⟩
      rcases nextData with ⟨nextYEq, nextXLt⟩
      change firstY = centerY at firstYEq
      change centerX < firstX at firstXLt
      change centerY = nextY at nextYEq
      change centerX < nextX at nextXLt
      apply Or.inl
      simp [GridSegment.IsHorizontal,
        GridSegment.OpenIntervalsOverlap,
        firstYEq, nextYEq,
        min_eq_right firstXLt.le,
        max_eq_left firstXLt.le,
        min_eq_left nextXLt.le,
        max_eq_right nextXLt.le,
        firstXLt, nextXLt]
      constructor <;> omega
  | south =>
      have firstData :=
        (between_eq_south_iff first center).mp incoming
      have nextData :=
        (between_eq_north_iff center next).mp (by
          simpa [incoming, opposite] using reversal)
      rcases first with ⟨firstX, firstY⟩
      rcases center with ⟨centerX, centerY⟩
      rcases next with ⟨nextX, nextY⟩
      rcases firstData with ⟨firstXEq, firstYLt⟩
      rcases nextData with ⟨nextXEq, nextYLt⟩
      change firstX = centerX at firstXEq
      change centerY < firstY at firstYLt
      change centerX = nextX at nextXEq
      change centerY < nextY at nextYLt
      apply Or.inr
      apply Or.inl
      simp [GridSegment.IsVertical,
        GridSegment.OpenIntervalsOverlap,
        firstXEq, nextXEq,
        min_eq_right firstYLt.le,
        max_eq_left firstYLt.le,
        min_eq_left nextYLt.le,
        max_eq_right nextYLt.le,
        firstYLt, nextYLt]
      constructor <;> omega
  | invalid =>
      exact (incomingGenuine incoming).elim

end AxisDirection

/-- Distinct syntactic segments of one route have disjoint continuous
interiors. -/
def RouteSegmentsHaveDisjointInteriors
    (points : List Cell) : Prop :=
  ∀ first second :
      Fin (gridPolylineSegments points).length,
    first ≠ second →
      ¬GridSegment.InteriorsMeet
        ((gridPolylineSegments points).get first)
        ((gridPolylineSegments points).get second)

/-- Restrict pairwise segment separation to the route tail. -/
theorem RouteSegmentsHaveDisjointInteriors.tail
    {first second : Cell} {rest : List Cell}
    (disjoint :
      RouteSegmentsHaveDisjointInteriors
        (first :: second :: rest)) :
    RouteSegmentsHaveDisjointInteriors
      (second :: rest) := by
  intro firstIndex secondIndex different
  let liftedFirst :
      Fin (gridPolylineSegments
        (first :: second :: rest)).length :=
    ⟨firstIndex.val + 1, by
      simpa [gridPolylineSegments] using
        Nat.add_lt_add_right firstIndex.isLt 1⟩
  let liftedSecond :
      Fin (gridPolylineSegments
        (first :: second :: rest)).length :=
    ⟨secondIndex.val + 1, by
      simpa [gridPolylineSegments] using
        Nat.add_lt_add_right secondIndex.isLt 1⟩
  have liftedDifferent : liftedFirst ≠ liftedSecond := by
    intro equal
    apply different
    apply Fin.ext
    have := congrArg Fin.val equal
    simp [liftedFirst, liftedSecond] at this
    omega
  simpa [gridPolylineSegments, liftedFirst, liftedSecond] using
    disjoint liftedFirst liftedSecond liftedDifferent

/-- Pairwise continuous separation of an orthogonal route excludes every
immediate reversal. -/
theorem AxisDirection.hasNoImmediateReversal_of_disjointInteriors
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (disjoint :
      RouteSegmentsHaveDisjointInteriors points) :
    AxisDirection.HasNoImmediateReversal points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [AxisDirection.HasNoImmediateReversal]
  | cons_cons first center rest _ tailInduction =>
      cases rest with
      | nil =>
          simp [AxisDirection.HasNoImmediateReversal]
      | cons next rest =>
          have orthogonalParts :=
            (List.isChain_cons_cons.mp orthogonal :
              (GridSegment.mk first center).IsAxisAligned ∧
                PeriodicOrthocrossing.OrthogonalPolyline
                  (center :: next :: rest))
          have nextAligned :=
            (List.isChain_cons_cons.mp orthogonalParts.2).1
          constructor
          · intro reversal
            let firstIndex :
                Fin (gridPolylineSegments
                  (first :: center :: next :: rest)).length :=
              ⟨0, by simp [gridPolylineSegments]⟩
            let secondIndex :
                Fin (gridPolylineSegments
                  (first :: center :: next :: rest)).length :=
              ⟨1, by simp [gridPolylineSegments]⟩
            apply disjoint firstIndex secondIndex (by
              intro equal
              have := congrArg Fin.val equal
              simp [firstIndex, secondIndex] at this)
            simpa [gridPolylineSegments, firstIndex, secondIndex] using
              AxisDirection.interiorsMeet_of_immediateReversal
                (AxisDirection.between_isGenuine_of_axisAligned
                  orthogonalParts.1)
                reversal
          · exact
              tailInduction center orthogonalParts.2
                disjoint.tail

namespace PeriodicGridDrawing

/-- Select one syntactic segment occurrence of a route stored at a genuine
drawing index. -/
theorem indexedSegment_getElem_mem
    (drawing : PeriodicGridDrawing)
    {routeIndex : Nat}
    (routeIndexLt : routeIndex < drawing.edgeRoutes.length)
    (segmentIndex :
      Fin (gridPolylineSegments
        drawing.edgeRoutes[routeIndex]).length) :
    let indexed : IndexedGridSegment :=
      ⟨routeIndex, segmentIndex.val,
        (gridPolylineSegments
          drawing.edgeRoutes[routeIndex]).get segmentIndex⟩
    indexed ∈ drawing.indexedSegments := by
  let route := drawing.edgeRoutes[routeIndex]
  let segment :=
    (gridPolylineSegments route).get segmentIndex
  have routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx := by
    have member :=
      List.getElem_mem (l := drawing.edgeRoutes.zipIdx)
        (n := routeIndex) (by simpa)
    simpa [route] using member
  have segmentMember :
      (segment, segmentIndex.val) ∈
        (gridPolylineSegments route).zipIdx := by
    have member :=
      List.getElem_mem
        (l := (gridPolylineSegments route).zipIdx)
        (n := segmentIndex.val) (by
          have indexLt :
              segmentIndex.val <
                (gridPolylineSegments
                  drawing.edgeRoutes[routeIndex]).length :=
            segmentIndex.isLt
          simpa [route] using indexLt)
    simpa [segment] using member
  unfold indexedSegments
  apply List.mem_flatMap.mpr
  refine ⟨(route, routeIndex), routeMember, ?_⟩
  apply List.mem_map.mpr
  exact
    ⟨(segment, segmentIndex.val),
      segmentMember, rfl⟩

/-- Continuous planarity gives pairwise continuous separation within every
stored route. -/
theorem IsContinuouslyPlanar.routeSegmentsHaveDisjointInteriors
    {drawing : PeriodicGridDrawing}
    (planar : drawing.IsContinuouslyPlanar)
    {routeIndex : Nat}
    (routeIndexLt : routeIndex < drawing.edgeRoutes.length) :
    RouteSegmentsHaveDisjointInteriors
      drawing.edgeRoutes[routeIndex] := by
  intro firstIndex secondIndex different
  let first : IndexedGridSegment :=
    ⟨routeIndex, firstIndex.val,
      (gridPolylineSegments
        drawing.edgeRoutes[routeIndex]).get firstIndex⟩
  let second : IndexedGridSegment :=
    ⟨routeIndex, secondIndex.val,
      (gridPolylineSegments
        drawing.edgeRoutes[routeIndex]).get secondIndex⟩
  have firstMember :=
    indexedSegment_getElem_mem drawing
      routeIndexLt firstIndex
  have secondMember :=
    indexedSegment_getElem_mem drawing
      routeIndexLt secondIndex
  have keysDifferent :
      SegmentOccurrenceKey first (0, 0) ≠
        SegmentOccurrenceKey second (0, 0) := by
    intro equal
    apply different
    apply Fin.ext
    have indexEqual :=
      congrArg (fun key => key.2.1) equal
    simpa [SegmentOccurrenceKey, first, second] using indexEqual
  simpa [first, second, GridSegment.translate,
    periodTranslation, Cell.add, Cell.scale] using
    planar.noInteriorsMeet firstMember secondMember
      keysDifferent

/-- Every orthogonal route stored by a continuously planar drawing has no
immediate reversal. -/
theorem IsContinuouslyPlanar.routeHasNoImmediateReversal
    {drawing : PeriodicGridDrawing}
    (planar : drawing.IsContinuouslyPlanar)
    (orthogonal : drawing.IsOrthogonal)
    {routeIndex : Nat}
    (routeIndexLt : routeIndex < drawing.edgeRoutes.length) :
    AxisDirection.HasNoImmediateReversal
      drawing.edgeRoutes[routeIndex] := by
  apply AxisDirection.hasNoImmediateReversal_of_disjointInteriors
  · rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
    intro segment segmentMember
    let segmentIndex :=
      (gridPolylineSegments
        drawing.edgeRoutes[routeIndex]).idxOf segment
    have segmentIndexLt :
        segmentIndex <
          (gridPolylineSegments
            drawing.edgeRoutes[routeIndex]).length :=
      List.idxOf_lt_length_iff.mpr segmentMember
    let indexed : IndexedGridSegment :=
      ⟨routeIndex, segmentIndex, segment⟩
    apply orthogonal indexed
    have indexedMember :=
      indexedSegment_getElem_mem drawing routeIndexLt
        ⟨segmentIndex, segmentIndexLt⟩
    have segmentLookup :
        (gridPolylineSegments
          drawing.edgeRoutes[routeIndex])[segmentIndex] =
            segment :=
      List.getElem_idxOf segmentIndexLt
    simpa [indexed, segmentLookup] using indexedMember
  · exact planar.routeSegmentsHaveDisjointInteriors
      routeIndexLt

end PeriodicGridDrawing
end LeanTrominoes
