import LeanTrominoes.PeriodicOrthocrossingCertified
import LeanTrominoes.PeriodicOrthocrossingCrossoverCenterDisjointness
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Continuous separation of parallel source segments

The integer-point orthocrossing certificate deliberately ignores open
overlap shorter than one grid cell.  Physical gadget corridors need the
continuous statement.  The constructed drawing has even horizontal
coordinates, so any continuous overlap of horizontal segment interiors
contains an integer grid point and is already covered by the established
private-lane theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- There is still an integer strictly between two distinct even integers. -/
theorem add_one_lt_of_even_of_even_of_lt
    {first second : Int}
    (firstEven : Even first)
    (secondEven : Even second)
    (less : first < second) :
    first + 1 < second := by
  rcases firstEven with ⟨firstHalf, firstEq⟩
  rcases secondEven with ⟨secondHalf, secondEq⟩
  omega

/-- The minimum of two even integers is even. -/
theorem even_min {first second : Int}
    (firstEven : Even first) (secondEven : Even second) :
    Even (min first second) := by
  rcases le_total first second with ordered | ordered
  · simpa [min_eq_left ordered] using firstEven
  · simpa [min_eq_right ordered] using secondEven

/-- The maximum of two even integers is even. -/
theorem even_max {first second : Int}
    (firstEven : Even first) (secondEven : Even second) :
    Even (max first second) := by
  rcases le_total first second with ordered | ordered
  · simpa [max_eq_right ordered] using secondEven
  · simpa [max_eq_left ordered] using firstEven

/-- Two nondegenerate open intervals with even endpoints have a common
integer interior point whenever their continuous interiors overlap. -/
theorem
    exists_common_strictlyBetween_of_openIntervalsOverlap_of_even_endpoints
    {firstStart firstFinish secondStart secondFinish : Int}
    (firstDifferent : firstStart ≠ firstFinish)
    (secondDifferent : secondStart ≠ secondFinish)
    (firstStartEven : Even firstStart)
    (firstFinishEven : Even firstFinish)
    (secondStartEven : Even secondStart)
    (secondFinishEven : Even secondFinish)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish) :
    ∃ point,
      GridSegment.StrictlyBetween firstStart firstFinish point ∧
        GridSegment.StrictlyBetween secondStart secondFinish point := by
  let firstLower := min firstStart firstFinish
  let firstUpper := max firstStart firstFinish
  let secondLower := min secondStart secondFinish
  let secondUpper := max secondStart secondFinish
  let lower := max firstLower secondLower
  have firstLowerEven : Even firstLower :=
    even_min firstStartEven firstFinishEven
  have firstUpperEven : Even firstUpper :=
    even_max firstStartEven firstFinishEven
  have secondLowerEven : Even secondLower :=
    even_min secondStartEven secondFinishEven
  have secondUpperEven : Even secondUpper :=
    even_max secondStartEven secondFinishEven
  have lowerEven : Even lower :=
    even_max firstLowerEven secondLowerEven
  have firstNonempty : firstLower < firstUpper := by
    simp only [firstLower, firstUpper]
    rcases lt_or_gt_of_ne firstDifferent with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have secondNonempty : secondLower < secondUpper := by
    simp only [secondLower, secondUpper]
    rcases lt_or_gt_of_ne secondDifferent with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have overlap' :
      firstLower < secondUpper ∧ secondLower < firstUpper := by
    simpa [GridSegment.OpenIntervalsOverlap,
      firstLower, firstUpper, secondLower, secondUpper] using overlap
  have lowerLtFirstUpper : lower < firstUpper := by
    simp only [lower, max_lt_iff]
    exact ⟨firstNonempty, overlap'.2⟩
  have lowerLtSecondUpper : lower < secondUpper := by
    simp only [lower, max_lt_iff]
    exact ⟨overlap'.1, secondNonempty⟩
  have pointLtFirstUpper : lower + 1 < firstUpper :=
    add_one_lt_of_even_of_even_of_lt
      lowerEven firstUpperEven lowerLtFirstUpper
  have pointLtSecondUpper : lower + 1 < secondUpper :=
    add_one_lt_of_even_of_even_of_lt
      lowerEven secondUpperEven lowerLtSecondUpper
  have firstLowerLtPoint : firstLower < lower + 1 := by
    have : firstLower ≤ lower := by
      simp [lower]
    omega
  have secondLowerLtPoint : secondLower < lower + 1 := by
    have : secondLower ≤ lower := by
      simp [lower]
    omega
  refine ⟨lower + 1, ?_, ?_⟩
  · unfold GridSegment.StrictlyBetween
    rcases lt_or_gt_of_ne firstDifferent with forward | backward
    · left
      simpa [firstLower, firstUpper,
        min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)] using
          And.intro firstLowerLtPoint pointLtFirstUpper
    · right
      simpa [firstLower, firstUpper,
        min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)] using
          And.intro firstLowerLtPoint pointLtFirstUpper
  · unfold GridSegment.StrictlyBetween
    rcases lt_or_gt_of_ne secondDifferent with forward | backward
    · left
      simpa [secondLower, secondUpper,
        min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)] using
          And.intro secondLowerLtPoint pointLtSecondUpper
    · right
      simpa [secondLower, secondUpper,
        min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)] using
          And.intro secondLowerLtPoint pointLtSecondUpper

/-- Both horizontal coordinates of every translated constructed horizontal
segment are even. -/
theorem classifiedSegment_horizontal_translated_endpoints_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.segment.IsHorizontal)
    (translate : Cell) :
    Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).start.1) ∧
      Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).finish.1) := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal] at itemHorizontal
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · norm_num [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
          parity_simps]
      · simp [GridSegment.IsHorizontal] at itemHorizontal
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    simp [classifiedEdgeCore] at itemMem
    all_goals try split at itemMem
    all_goals try split at itemMem
    all_goals try simp only [List.mem_cons] at itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try simp at itemMem
    all_goals norm_num [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
      edgeGateX, parity_simps]
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    have itemFullMem :
        item ∈ classifiedRouteSegments graph edge edgeIndex := by
      simp [classifiedRouteSegments, itemMem]
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
        at itemHorizontal
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
          at itemHorizontal
      · exact horizontalFanout_translated_endpoints_even
          itemFullMem (by
            simp [SegmentRole.IsHorizontalFanout]) translate
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem horizontal)
      (fun coreMem =>
        coreAll classified coreMem horizontal))
    (fun targetMem =>
      targetAll classified targetMem horizontal)

/-- Both horizontal coordinates of a translated drawing-segment occurrence
are even. -/
theorem drawing_horizontal_translated_endpoints_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (translate : Cell)
    (horizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).IsHorizontal)
    :
    Even
        ((indexed.segment.translate
          ((drawing graph).periodTranslation translate)).start.1) ∧
      Even
        ((indexed.segment.translate
          ((drawing graph).periodTranslation translate)).finish.1) := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨route, routeMem, classified, classifiedMem, indexedEq⟩
  subst indexed
  have storedHorizontal :
      classified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp horizontal
  exact classifiedSegment_horizontal_translated_endpoints_even
    (List.fst_mem_of_mem_zipIdx classifiedMem)
    storedHorizontal translate

/-- Continuous overlap of two horizontal constructed occurrences contains
an integer grid point, so the existing private-lane certificate identifies
their occurrence keys. -/
theorem drawing_hasUniqueHorizontalContinuousInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ first ∈ (drawing graph).indexedSegments,
      ∀ second ∈ (drawing graph).indexedSegments,
        ∀ firstTranslate secondTranslate,
          (first.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).IsHorizontal →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).IsHorizontal →
          GridSegment.InteriorsMeet
              (first.segment.translate
                ((drawing graph).periodTranslation firstTranslate))
              (second.segment.translate
                ((drawing graph).periodTranslation secondTranslate)) →
          PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey
              second secondTranslate := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate firstHorizontal secondHorizontal meet
  let firstSegment :=
    first.segment.translate
      ((drawing graph).periodTranslation firstTranslate)
  let secondSegment :=
    second.segment.translate
      ((drawing graph).periodTranslation secondTranslate)
  have firstEven :=
    drawing_horizontal_translated_endpoints_even
      firstMem firstTranslate firstHorizontal
  have secondEven :=
    drawing_horizontal_translated_endpoints_even
      secondMem secondTranslate secondHorizontal
  have horizontalMeet :
      firstSegment.IsHorizontal ∧ secondSegment.IsHorizontal ∧
        firstSegment.start.2 = secondSegment.start.2 ∧
        GridSegment.OpenIntervalsOverlap
          firstSegment.start.1 firstSegment.finish.1
          secondSegment.start.1 secondSegment.finish.1 := by
    rcases meet with
      horizontal | vertical | horizontalVertical | verticalHorizontal
    · exact horizontal
    · exact False.elim (firstHorizontal.2 vertical.1.1)
    · exact False.elim (secondHorizontal.2 horizontalVertical.2.1.1)
    · exact False.elim (firstHorizontal.2 verticalHorizontal.1.1)
  rcases
      exists_common_strictlyBetween_of_openIntervalsOverlap_of_even_endpoints
        firstHorizontal.2 secondHorizontal.2
        firstEven.1 firstEven.2 secondEven.1 secondEven.2
        horizontalMeet.2.2.2 with
    ⟨pointX, firstBetween, secondBetween⟩
  let point : Cell := (pointX, firstSegment.start.2)
  have firstContains : firstSegment.InteriorContains point := by
    exact Or.inl
      ⟨firstHorizontal, rfl, firstBetween⟩
  have secondContains : secondSegment.InteriorContains point := by
    apply Or.inl
    refine ⟨secondHorizontal, ?_, secondBetween⟩
    simpa [point] using horizontalMeet.2.2.1
  exact drawing_hasUniqueHorizontalInteriors
    wellFormed degree isLocal
    first firstMem second secondMem
    firstTranslate secondTranslate point
    firstContains secondContains firstHorizontal secondHorizontal

/-- Distinct horizontal segment occurrences in the constructed drawing have
disjoint continuous relative interiors. -/
theorem drawing_horizontalContinuousInteriors_disjoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    {firstTranslate secondTranslate : Cell}
    (firstHorizontal :
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsHorizontal)
    (secondHorizontal :
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsHorizontal)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate) :
    ¬GridSegment.InteriorsMeet
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate))
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)) := by
  intro meet
  exact different
    (drawing_hasUniqueHorizontalContinuousInteriors
      wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate
      firstHorizontal secondHorizontal meet)

end PeriodicOrthocrossing
end LeanTrominoes
