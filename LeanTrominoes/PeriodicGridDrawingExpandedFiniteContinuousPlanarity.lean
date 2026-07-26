import LeanTrominoes.PeriodicGridDrawingExpandedFinitePlanarity

/-!
# Continuous planarity checking for halo-bounded periodic routes

This file adds exact relative-interior separation to the expanded finite
checker.  Open interval overlap between two halo-bounded segments also limits
their relative translation to `[-2,2]` in each coordinate, so the same 25
checks certify continuous planarity of the infinite periodic lift.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- Overlap of a translated halo interval with another halo interval bounds
the relative period shift by two. -/
theorem overlap_shift_is_doubleNeighbor
    {period firstStart firstFinish secondStart secondFinish shift : Int}
    (periodPositive : 0 < period)
    (firstStartLower : -period < firstStart)
    (firstStartUpper : firstStart < 2 * period)
    (firstFinishLower : -period < firstFinish)
    (firstFinishUpper : firstFinish < 2 * period)
    (secondStartLower : -period < secondStart)
    (secondStartUpper : secondStart < 2 * period)
    (secondFinishLower : -period < secondFinish)
    (secondFinishUpper : secondFinish < 2 * period)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        (firstStart + period * shift)
        (firstFinish + period * shift)
        secondStart secondFinish) :
    -2 ≤ shift ∧ shift ≤ 2 := by
  unfold GridSegment.OpenIntervalsOverlap at overlap
  rw [min_add_add_right, max_add_add_right] at overlap
  have firstMinLower :
      -period < min firstStart firstFinish :=
    lt_min firstStartLower firstFinishLower
  have firstMaxUpper :
      max firstStart firstFinish < 2 * period :=
    max_lt firstStartUpper firstFinishUpper
  have secondMinLower :
      -period < min secondStart secondFinish :=
    lt_min secondStartLower secondFinishLower
  have secondMaxUpper :
      max secondStart secondFinish < 2 * period :=
    max_lt secondStartUpper secondFinishUpper
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -3 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -3 * period := by
      nlinarith
    omega
  · by_contra tooHigh
    have shiftHigh : 3 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        3 * period ≤ period * shift := by
      nlinarith
    omega

/-- A continuous relative-interior contact between two halo-bounded
occurrences also has one of the 25 bounded relative translations. -/
theorem relativeTranslate_isDoubleNeighbor_of_interiorsMeet
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate : Cell}
    (meet :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation firstTranslate))
        (second.segment.translate
          (drawing.periodTranslation secondTranslate))) :
    Cell.sub firstTranslate secondTranslate ∈
      doubleNeighborTranslations := by
  let relative := Cell.sub firstTranslate secondTranslate
  have normalized :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation relative))
        second.segment :=
    (interiorsMeet_normalize drawing first.segment second.segment
      firstTranslate secondTranslate).mp meet
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := endpointBounds first firstMember
  have secondBounds := endpointBounds second secondMember
  apply (mem_doubleNeighborTranslations_iff relative).mpr
  rcases firstBounds with ⟨firstStartBounds, firstFinishBounds⟩
  rcases secondBounds with ⟨secondStartBounds, secondFinishBounds⟩
  rcases firstStartBounds with
    ⟨firstStartXLower, firstStartXUpper,
      firstStartYLower, firstStartYUpper⟩
  rcases firstFinishBounds with
    ⟨firstFinishXLower, firstFinishXUpper,
      firstFinishYLower, firstFinishYUpper⟩
  rcases secondStartBounds with
    ⟨secondStartXLower, secondStartXUpper,
      secondStartYLower, secondStartYUpper⟩
  rcases secondFinishBounds with
    ⟨secondFinishXLower, secondFinishXUpper,
      secondFinishYLower, secondFinishYUpper⟩
  rcases normalized with
      ⟨firstHorizontal, secondHorizontal, sameY, horizontalOverlap⟩ |
      ⟨firstVertical, secondVertical, sameX, verticalOverlap⟩ |
      ⟨firstHorizontal, secondVertical, xBetween, yBetween⟩ |
      ⟨firstVertical, secondHorizontal, xBetween, yBetween⟩
  · have overlap :
        GridSegment.OpenIntervalsOverlap
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          second.segment.start.1 second.segment.finish.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using horizontalOverlap
    have lane :
        second.segment.start.2 =
          first.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using sameY.symm
    exact
      ⟨overlap_shift_is_doubleNeighbor periodPositive
          firstStartXLower firstStartXUpper
          firstFinishXLower firstFinishXUpper
          secondStartXLower secondStartXUpper
          secondFinishXLower secondFinishXUpper overlap,
        lane_shift_is_doubleNeighbor periodPositive
          firstStartYLower firstStartYUpper
          secondStartYLower secondStartYUpper lane⟩
  · have lane :
        second.segment.start.1 =
          first.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using sameX.symm
    have overlap :
        GridSegment.OpenIntervalsOverlap
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          second.segment.start.2 second.segment.finish.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using verticalOverlap
    exact
      ⟨lane_shift_is_doubleNeighbor periodPositive
          firstStartXLower firstStartXUpper
          secondStartXLower secondStartXUpper lane,
        overlap_shift_is_doubleNeighbor periodPositive
          firstStartYLower firstStartYUpper
          firstFinishYLower firstFinishYUpper
          secondStartYLower secondStartYUpper
          secondFinishYLower secondFinishYUpper overlap⟩
  · have horizontalBetween :
        GridSegment.StrictlyBetween
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          second.segment.start.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using xBetween
    have translatedYLower :
        -(drawing.gridSize : Int) <
          first.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at yBetween
      unfold GridSegment.StrictlyBetween at yBetween
      rcases yBetween with yBetween | yBetween <;> omega
    have translatedYUpper :
        first.segment.start.2 +
            drawing.gridSize * relative.2 <
          2 * drawing.gridSize := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at yBetween
      unfold GridSegment.StrictlyBetween at yBetween
      rcases yBetween with yBetween | yBetween <;> omega
    exact
      ⟨between_shift_is_doubleNeighbor periodPositive
          firstStartXLower firstStartXUpper
          firstFinishXLower firstFinishXUpper
          secondStartXLower secondStartXUpper horizontalBetween,
        lane_shift_is_doubleNeighbor periodPositive
          firstStartYLower firstStartYUpper
          translatedYLower translatedYUpper rfl⟩
  · have translatedXLower :
        -(drawing.gridSize : Int) <
          first.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at xBetween
      unfold GridSegment.StrictlyBetween at xBetween
      rcases xBetween with xBetween | xBetween <;> omega
    have translatedXUpper :
        first.segment.start.1 +
            drawing.gridSize * relative.1 <
          2 * drawing.gridSize := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at xBetween
      unfold GridSegment.StrictlyBetween at xBetween
      rcases xBetween with xBetween | xBetween <;> omega
    have verticalBetween :
        GridSegment.StrictlyBetween
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          second.segment.start.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using yBetween
    exact
      ⟨lane_shift_is_doubleNeighbor periodPositive
          firstStartXLower firstStartXUpper
          translatedXLower translatedXUpper rfl,
        between_shift_is_doubleNeighbor periodPositive
          firstStartYLower firstStartYUpper
          firstFinishYLower firstFinishYUpper
          secondStartYLower secondStartYUpper verticalBetween⟩

/-- Exact finite continuous-interior check over all 25 allowed relative
translations. -/
def expandedFiniteRoutesHaveDisjointInteriors
    (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun first =>
    drawing.indexedSegments.all fun second =>
      doubleNeighborTranslations.all fun relative =>
        decide
          (SegmentOccurrenceKey first relative =
              SegmentOccurrenceKey second (0, 0) ∨
            ¬GridSegment.InteriorsMeet
              (first.segment.translate
                (drawing.periodTranslation relative))
              second.segment)

theorem expandedFiniteRoutesHaveDisjointInteriors_spec
    {drawing : PeriodicGridDrawing}
    (checked :
      drawing.expandedFiniteRoutesHaveDisjointInteriors = true) :
    ∀ first ∈ drawing.indexedSegments,
      ∀ second ∈ drawing.indexedSegments,
        ∀ relative ∈ doubleNeighborTranslations,
          SegmentOccurrenceKey first relative =
              SegmentOccurrenceKey second (0, 0) ∨
            ¬GridSegment.InteriorsMeet
              (first.segment.translate
                (drawing.periodTranslation relative))
              second.segment := by
  simpa [expandedFiniteRoutesHaveDisjointInteriors] using checked

/-- The 25 finite checks prove global continuous route-interior separation. -/
theorem routesHaveDisjointInteriors_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    (checked :
      drawing.expandedFiniteRoutesHaveDisjointInteriors = true) :
    drawing.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate different meet
  let relative := Cell.sub firstTranslate secondTranslate
  have relativeMember :=
    relativeTranslate_isDoubleNeighbor_of_interiorsMeet
      endpointBounds firstMember secondMember meet
  have normalized :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation relative))
        second.segment :=
    (interiorsMeet_normalize drawing first.segment second.segment
      firstTranslate secondTranslate).mp meet
  rcases expandedFiniteRoutesHaveDisjointInteriors_spec checked
      first firstMember second secondMember
      relative relativeMember with same | avoids
  · exact relative_key_ne different same
  · exact avoids normalized

/-- The expanded integer and continuous checks certify exact continuous
planarity of the infinite periodic lift. -/
theorem isContinuouslyPlanar_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (routesChecked :
      drawing.expandedFiniteRoutesAvoidInteriors = true)
    (verticesChecked :
      drawing.finiteVerticesAvoidRouteInteriors = true)
    (continuousChecked :
      drawing.expandedFiniteRoutesHaveDisjointInteriors = true) :
    drawing.IsContinuouslyPlanar :=
  ⟨isPlanar_of_expandedFinite endpointBounds vertexBounds
      routesChecked verticesChecked,
    routesHaveDisjointInteriors_of_expandedFinite
      endpointBounds continuousChecked⟩

end PeriodicGridDrawing
end LeanTrominoes
