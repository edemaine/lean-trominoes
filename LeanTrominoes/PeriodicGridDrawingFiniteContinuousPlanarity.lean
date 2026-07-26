import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity
import LeanTrominoes.PeriodicGridDrawingFinitePlanarity

/-!
# Finite checking of continuous periodic route separation

This file extends the neighboring-translation planarity checker with the
continuous collinear-overlap test.  Segment endpoints in one fundamental
square imply that any pair of intersecting open segment interiors differs
by one of the nine neighboring lattice translations.  The resulting Boolean
check therefore proves `RoutesHaveDisjointInteriors` globally.
-/

namespace LeanTrominoes

namespace PeriodicOrthocrossing

/-- If two open intervals with endpoints in one fundamental interval overlap
after translating the first by whole periods, that translation is a
neighboring one. -/
theorem overlap_shift_is_neighbor
    {period firstStart firstFinish secondStart secondFinish shift : Int}
    (periodPositive : 0 < period)
    (firstStartLower : 0 < firstStart)
    (firstStartUpper : firstStart < period)
    (firstFinishLower : 0 < firstFinish)
    (firstFinishUpper : firstFinish < period)
    (secondStartLower : 0 < secondStart)
    (secondStartUpper : secondStart < period)
    (secondFinishLower : 0 < secondFinish)
    (secondFinishUpper : secondFinish < period)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        (firstStart + period * shift)
        (firstFinish + period * shift)
        secondStart secondFinish) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  unfold GridSegment.OpenIntervalsOverlap at overlap
  rw [min_add_add_right, max_add_add_right] at overlap
  have firstMinLower :
      0 < min firstStart firstFinish :=
    lt_min firstStartLower firstFinishLower
  have firstMaxUpper :
      max firstStart firstFinish < period :=
    max_lt firstStartUpper firstFinishUpper
  have secondMinLower :
      0 < min secondStart secondFinish :=
    lt_min secondStartLower secondFinishLower
  have secondMaxUpper :
      max secondStart secondFinish < period :=
    max_lt secondStartUpper secondFinishUpper
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    omega
  omega

end PeriodicOrthocrossing

namespace PeriodicGridDrawing

open PeriodicOrthocrossing

/-- Normalizing both periodic occurrences by the second translation
preserves continuous interior intersection. -/
theorem interiorsMeet_normalize
    (drawing : PeriodicGridDrawing)
    (first second : GridSegment)
    (firstTranslate secondTranslate : Cell) :
    GridSegment.InteriorsMeet
        (first.translate
          (drawing.periodTranslation firstTranslate))
        (second.translate
          (drawing.periodTranslation secondTranslate)) ↔
      GridSegment.InteriorsMeet
        (first.translate
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate)))
        second := by
  let relative := Cell.sub firstTranslate secondTranslate
  let offset := drawing.periodTranslation secondTranslate
  have firstEq :
      (first.translate
        (drawing.periodTranslation relative)).translate offset =
          first.translate
            (drawing.periodTranslation firstTranslate) := by
    exact translate_relative
      drawing first firstTranslate secondTranslate
  have secondEq :
      second.translate offset =
        second.translate
          (drawing.periodTranslation secondTranslate) := rfl
  rw [← firstEq, ← secondEq]
  exact GridSegment.interiorsMeet_translate_both_iff
    (first.translate (drawing.periodTranslation relative))
    second offset

/-- A continuous contact between two fundamental-square segment occurrences
has a neighboring relative translation. -/
theorem relativeTranslate_isNeighbor_of_interiorsMeet
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
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
    Cell.sub firstTranslate secondTranslate ∈ neighborTranslations := by
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
  apply (mem_neighborTranslations_iff relative).mpr
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
      ⟨overlap_shift_is_neighbor periodPositive
          firstStartXLower firstStartXUpper
          firstFinishXLower firstFinishXUpper
          secondStartXLower secondStartXUpper
          secondFinishXLower secondFinishXUpper overlap,
        lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          (by omega) (by omega) lane⟩
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
      ⟨lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          (by omega) (by omega) lane,
        overlap_shift_is_neighbor periodPositive
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
        0 ≤ first.segment.start.2 +
          drawing.gridSize * relative.2 := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at yBetween
      unfold GridSegment.StrictlyBetween at yBetween
      rcases yBetween with yBetween | yBetween <;> omega
    have translatedYUpper :
        first.segment.start.2 +
            drawing.gridSize * relative.2 <
          drawing.gridSize := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at yBetween
      unfold GridSegment.StrictlyBetween at yBetween
      rcases yBetween with yBetween | yBetween <;> omega
    exact
      ⟨between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) horizontalBetween,
        lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          translatedYLower translatedYUpper rfl⟩
  · have translatedXLower :
        0 ≤ first.segment.start.1 +
          drawing.gridSize * relative.1 := by
      simp only [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale] at xBetween
      unfold GridSegment.StrictlyBetween at xBetween
      rcases xBetween with xBetween | xBetween <;> omega
    have translatedXUpper :
        first.segment.start.1 +
            drawing.gridSize * relative.1 <
          drawing.gridSize := by
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
      ⟨lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          translatedXLower translatedXUpper rfl,
        between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) verticalBetween⟩

/-- Exact finite check for continuous relative-interior separation. -/
def finiteRoutesHaveDisjointInteriors
    (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun first =>
    drawing.indexedSegments.all fun second =>
      neighborTranslations.all fun relative =>
        decide
          (SegmentOccurrenceKey first relative =
              SegmentOccurrenceKey second (0, 0) ∨
            ¬GridSegment.InteriorsMeet
              (first.segment.translate
                (drawing.periodTranslation relative))
              second.segment)

theorem finiteRoutesHaveDisjointInteriors_spec
    {drawing : PeriodicGridDrawing}
    (checked :
      drawing.finiteRoutesHaveDisjointInteriors = true) :
    ∀ first ∈ drawing.indexedSegments,
      ∀ second ∈ drawing.indexedSegments,
        ∀ relative ∈ neighborTranslations,
          SegmentOccurrenceKey first relative =
              SegmentOccurrenceKey second (0, 0) ∨
            ¬GridSegment.InteriorsMeet
              (first.segment.translate
                (drawing.periodTranslation relative))
              second.segment := by
  simpa [finiteRoutesHaveDisjointInteriors] using checked

/-- The exact neighboring-translation check proves global continuous route
separation. -/
theorem routesHaveDisjointInteriors_of_finite
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (checked :
      drawing.finiteRoutesHaveDisjointInteriors = true) :
    drawing.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate different meet
  let relative := Cell.sub firstTranslate secondTranslate
  have relativeMember :=
    relativeTranslate_isNeighbor_of_interiorsMeet
      endpointBounds firstMember secondMember meet
  have normalized :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation relative))
        second.segment :=
    (interiorsMeet_normalize drawing first.segment second.segment
      firstTranslate secondTranslate).mp meet
  rcases finiteRoutesHaveDisjointInteriors_spec checked
      first firstMember second secondMember relative relativeMember with
    same | avoids
  · exact relative_key_ne different same
  · exact avoids normalized

/-- The three finite checks certify exact continuous periodic planarity. -/
theorem isContinuouslyPlanar_of_finite
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (routesChecked : drawing.finiteRoutesAvoidInteriors = true)
    (verticesChecked :
      drawing.finiteVerticesAvoidRouteInteriors = true)
    (continuousChecked :
      drawing.finiteRoutesHaveDisjointInteriors = true) :
    drawing.IsContinuouslyPlanar :=
  ⟨isPlanar_of_finite endpointBounds vertexBounds
      routesChecked verticesChecked,
    routesHaveDisjointInteriors_of_finite
      endpointBounds continuousChecked⟩

end PeriodicGridDrawing
end LeanTrominoes
