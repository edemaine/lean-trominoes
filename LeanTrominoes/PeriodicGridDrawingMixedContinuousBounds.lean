import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity

/-!
# Continuous contacts between fundamental and halo-bounded routes

Normalized noncarrier routes in the planar-SAT construction lie in the
half-open fundamental square, while carrier routes may use the surrounding
one-cell halo.  A continuous contact involving a half-open route can differ
by only one period in either coordinate.  Thus such mixed contacts use the
ordinary nine neighboring translations rather than all 25 translations
needed for two halo-bounded routes.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PeriodicOrthocrossing

/-- A point lies in the coordinatewise half-open fundamental square. -/
def PositionInHalfOpenFundamentalSquare
    (drawing : PeriodicGridDrawing) (position : Cell) : Prop :=
  0 ≤ position.1 ∧ position.1 < drawing.gridSize ∧
    0 ≤ position.2 ∧ position.2 < drawing.gridSize

/-- Both endpoints of every stored segment lie in the half-open
fundamental square. -/
def SegmentEndpointsInHalfOpenFundamentalSquare
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ indexed ∈ drawing.indexedSegments,
    drawing.PositionInHalfOpenFundamentalSquare indexed.segment.start ∧
      drawing.PositionInHalfOpenFundamentalSquare indexed.segment.finish

/-- Equality between a translated half-open coordinate and a halo
coordinate bounds the translation to `[-1, 1]`. -/
theorem lane_shift_isNeighbor_of_halfOpen_expanded
    {period first second shift : Int}
    (periodPositive : 0 < period)
    (firstLower : 0 ≤ first)
    (firstUpper : first < period)
    (secondLower : -period < second)
    (secondUpper : second < 2 * period)
    (equal : second = first + period * shift) :
    -1 ≤ shift ∧ shift ≤ 1 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -2 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    omega
  · by_contra tooHigh
    have shiftHigh : 2 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    omega

/-- Strict betweenness between translated half-open endpoints and a halo
coordinate has the same neighboring-shift bound. -/
theorem between_shift_isNeighbor_of_halfOpen_expanded
    {period first finish shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : 0 ≤ first)
    (firstUpper : first < period)
    (finishLower : 0 ≤ finish)
    (finishUpper : finish < period)
    (pointLower : -period < point)
    (pointUpper : point < 2 * period)
    (between :
      GridSegment.StrictlyBetween
        (first + period * shift)
        (finish + period * shift) point) :
    -1 ≤ shift ∧ shift ≤ 1 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -2 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega
  · by_contra tooHigh
    have shiftHigh : 2 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega

/-- Closed betweenness between translated half-open endpoints and a halo
coordinate also forces a neighboring translation. -/
theorem between_closed_shift_isNeighbor_of_halfOpen_expanded
    {period first finish shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : 0 ≤ first)
    (firstUpper : first < period)
    (finishLower : 0 ≤ finish)
    (finishUpper : finish < period)
    (pointLower : -period < point)
    (pointUpper : point < 2 * period)
    (between :
      GridSegment.Between
        (first + period * shift)
        (finish + period * shift) point) :
    -1 ≤ shift ∧ shift ≤ 1 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -2 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    unfold GridSegment.Between at between
    rcases between with between | between <;> omega
  · by_contra tooHigh
    have shiftHigh : 2 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.Between at between
    rcases between with between | between <;> omega

/-- If a translated half-open point lies strictly between two halo
coordinates, its translation is neighboring. -/
theorem translatedPoint_between_expanded_isNeighbor
    {period point shift first finish : Int}
    (periodPositive : 0 < period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (finishLower : -period < finish)
    (finishUpper : finish < 2 * period)
    (between :
      GridSegment.StrictlyBetween first finish
        (point + period * shift)) :
    -1 ≤ shift ∧ shift ≤ 1 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -2 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega
  · by_contra tooHigh
    have shiftHigh : 2 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega

/-- Open overlap between a translated half-open interval and a halo
interval also bounds the translation to `[-1, 1]`. -/
theorem overlap_shift_isNeighbor_of_halfOpen_expanded
    {period firstStart firstFinish secondStart secondFinish shift : Int}
    (periodPositive : 0 < period)
    (firstStartLower : 0 ≤ firstStart)
    (firstStartUpper : firstStart < period)
    (firstFinishLower : 0 ≤ firstFinish)
    (firstFinishUpper : firstFinish < period)
    (secondStartLower : -period < secondStart)
    (secondStartUpper : secondStart < 2 * period)
    (secondFinishLower : -period < secondFinish)
    (secondFinishUpper : secondFinish < 2 * period)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        (firstStart + period * shift)
        (firstFinish + period * shift)
        secondStart secondFinish) :
    -1 ≤ shift ∧ shift ≤ 1 := by
  unfold GridSegment.OpenIntervalsOverlap at overlap
  rw [min_add_add_right, max_add_add_right] at overlap
  have firstMinLower :
      0 ≤ min firstStart firstFinish :=
    le_min firstStartLower firstFinishLower
  have firstMaxUpper :
      max firstStart firstFinish < period :=
    max_lt firstStartUpper firstFinishUpper
  have secondMinLower :
      -period < min secondStart secondFinish :=
    lt_min secondStartLower secondFinishLower
  have secondMaxUpper :
      max secondStart secondFinish < 2 * period :=
    max_lt secondStartUpper secondFinishUpper
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -2 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -2 * period := by
      nlinarith
    omega
  · by_contra tooHigh
    have shiftHigh : 2 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        2 * period ≤ period * shift := by
      nlinarith
    omega

/-- A continuous contact between a half-open segment occurrence and a
halo-bounded occurrence has a neighboring relative translation. -/
theorem relativeTranslate_isNeighbor_of_interiorsMeet_of_firstHalfOpen
    {drawing : PeriodicGridDrawing}
    {first second : IndexedGridSegment}
    (firstBounds :
      drawing.PositionInHalfOpenFundamentalSquare first.segment.start ∧
        drawing.PositionInHalfOpenFundamentalSquare first.segment.finish)
    (secondBounds :
      drawing.PositionInExpandedSquare second.segment.start ∧
        drawing.PositionInExpandedSquare second.segment.finish)
    {firstTranslate secondTranslate : Cell}
    (meet :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation firstTranslate))
        (second.segment.translate
          (drawing.periodTranslation secondTranslate))) :
    Cell.sub firstTranslate secondTranslate ∈
      neighborTranslations := by
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
    have horizontalBounds :=
      overlap_shift_isNeighbor_of_halfOpen_expanded
        periodPositive
        firstStartXLower firstStartXUpper
        firstFinishXLower firstFinishXUpper
        secondStartXLower secondStartXUpper
        secondFinishXLower secondFinishXUpper overlap
    have verticalBounds :=
      lane_shift_isNeighbor_of_halfOpen_expanded
        periodPositive firstStartYLower firstStartYUpper
        secondStartYLower secondStartYUpper lane
    exact ⟨by omega, by omega⟩
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
    have horizontalBounds :=
      lane_shift_isNeighbor_of_halfOpen_expanded
        periodPositive firstStartXLower firstStartXUpper
        secondStartXLower secondStartXUpper lane
    have verticalBounds :=
      overlap_shift_isNeighbor_of_halfOpen_expanded
        periodPositive
        firstStartYLower firstStartYUpper
        firstFinishYLower firstFinishYUpper
        secondStartYLower secondStartYUpper
        secondFinishYLower secondFinishYUpper overlap
    exact ⟨by omega, by omega⟩
  · have horizontalBetween :
        GridSegment.StrictlyBetween
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          second.segment.start.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using xBetween
    have verticalBetween :
        GridSegment.StrictlyBetween
          second.segment.start.2 second.segment.finish.2
          (first.segment.start.2 +
            drawing.gridSize * relative.2) := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using yBetween
    have horizontalBounds :=
      between_shift_isNeighbor_of_halfOpen_expanded
        periodPositive
        firstStartXLower firstStartXUpper
        firstFinishXLower firstFinishXUpper
        secondStartXLower secondStartXUpper horizontalBetween
    have verticalBounds :=
      translatedPoint_between_expanded_isNeighbor
        periodPositive firstStartYLower firstStartYUpper
        secondStartYLower secondStartYUpper
        secondFinishYLower secondFinishYUpper verticalBetween
    exact ⟨by omega, by omega⟩
  · have horizontalBetween :
        GridSegment.StrictlyBetween
          second.segment.start.1 second.segment.finish.1
          (first.segment.start.1 +
            drawing.gridSize * relative.1) := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using xBetween
    have verticalBetween :
        GridSegment.StrictlyBetween
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          second.segment.start.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using yBetween
    have horizontalBounds :=
      translatedPoint_between_expanded_isNeighbor
        periodPositive firstStartXLower firstStartXUpper
        secondStartXLower secondStartXUpper
        secondFinishXLower secondFinishXUpper horizontalBetween
    have verticalBounds :=
      between_shift_isNeighbor_of_halfOpen_expanded
        periodPositive
        firstStartYLower firstStartYUpper
        firstFinishYLower firstFinishYUpper
        secondStartYLower secondStartYUpper verticalBetween
    exact ⟨by omega, by omega⟩

/-- Reversing a neighboring relative translation remains neighboring. -/
theorem isNeighborTranslation_sub_comm
    {first second : Cell}
    (neighbor :
      IsNeighborTranslation (Cell.sub second first)) :
    IsNeighborTranslation (Cell.sub first second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases neighbor with
    ⟨horizontalNeighbor, verticalNeighbor⟩
  simp only [Cell.sub] at horizontalNeighbor verticalNeighbor ⊢
  constructor
  · rcases horizontalNeighbor with
      horizontalNeighbor | horizontalNeighbor | horizontalNeighbor <;>
      omega
  · rcases verticalNeighbor with
      verticalNeighbor | verticalNeighbor | verticalNeighbor <;>
      omega

/-- The mixed neighboring-shift bound is symmetric in the two segment
occurrences. -/
theorem relativeTranslate_isNeighbor_of_interiorsMeet_of_secondHalfOpen
    {drawing : PeriodicGridDrawing}
    {first second : IndexedGridSegment}
    (firstBounds :
      drawing.PositionInExpandedSquare first.segment.start ∧
        drawing.PositionInExpandedSquare first.segment.finish)
    (secondBounds :
      drawing.PositionInHalfOpenFundamentalSquare second.segment.start ∧
        drawing.PositionInHalfOpenFundamentalSquare second.segment.finish)
    {firstTranslate secondTranslate : Cell}
    (meet :
      GridSegment.InteriorsMeet
        (first.segment.translate
          (drawing.periodTranslation firstTranslate))
        (second.segment.translate
          (drawing.periodTranslation secondTranslate))) :
    Cell.sub firstTranslate secondTranslate ∈
      neighborTranslations := by
  have reversed :
      Cell.sub secondTranslate firstTranslate ∈
        neighborTranslations :=
    relativeTranslate_isNeighbor_of_interiorsMeet_of_firstHalfOpen
      secondBounds firstBounds
      ((GridSegment.interiorsMeet_comm
        (first.segment.translate
          (drawing.periodTranslation firstTranslate))
        (second.segment.translate
          (drawing.periodTranslation secondTranslate))).mp meet)
  have reversedNeighbor :
      IsNeighborTranslation
        (Cell.sub secondTranslate firstTranslate) :=
    (mem_neighborTranslations_iff _).mp reversed
  exact
    (mem_neighborTranslations_iff _).mpr
      (isNeighborTranslation_sub_comm reversedNeighbor)

/-- An asymmetric carrier-interior/half-open-closed contact also has an
ordinary neighboring relative translation. -/
theorem relativeTranslate_isNeighbor_of_endpointContact_of_secondHalfOpen
    {drawing : PeriodicGridDrawing}
    {first second : IndexedGridSegment}
    (firstBounds :
      drawing.PositionInExpandedSquare first.segment.start ∧
        drawing.PositionInExpandedSquare first.segment.finish)
    (secondBounds :
      drawing.PositionInHalfOpenFundamentalSquare second.segment.start ∧
        drawing.PositionInHalfOpenFundamentalSquare second.segment.finish)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (first.segment.translate
        (drawing.periodTranslation firstTranslate)).InteriorContains point)
    (secondContains :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).Contains point) :
    Cell.sub firstTranslate secondTranslate ∈
      neighborTranslations := by
  let reverse := Cell.sub secondTranslate firstTranslate
  let normalized := drawing.normalizePoint point firstTranslate
  have normalizedFirst :
      first.segment.InteriorContains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (interiorContains_normalize drawing first.segment
        firstTranslate firstTranslate point).mp firstContains
  have normalizedSecond :
      (second.segment.translate
        (drawing.periodTranslation reverse)).Contains normalized :=
    (contains_normalize drawing second.segment
      secondTranslate firstTranslate point).mp secondContains
  have normalizedBounds :
      drawing.PositionInExpandedSquare normalized := by
    rcases firstBounds with ⟨firstStartBounds, firstFinishBounds⟩
    rcases firstStartBounds with
      ⟨firstStartXLower, firstStartXUpper,
        firstStartYLower, firstStartYUpper⟩
    rcases firstFinishBounds with
      ⟨firstFinishXLower, firstFinishXUpper,
        firstFinishYLower, firstFinishYUpper⟩
    rcases normalizedFirst with
        ⟨horizontal, sameY, betweenX⟩ |
        ⟨vertical, sameX, betweenY⟩
    · simp only [GridSegment.IsHorizontal] at horizontal
      rcases betweenX with betweenX | betweenX <;>
        exact ⟨by omega, by omega, by omega, by omega⟩
    · simp only [GridSegment.IsVertical] at vertical
      rcases betweenY with betweenY | betweenY <;>
        exact ⟨by omega, by omega, by omega, by omega⟩
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have reverseNeighbor : IsNeighborTranslation reverse := by
    rcases secondBounds with ⟨secondStartBounds, secondFinishBounds⟩
    rcases secondStartBounds with
      ⟨secondStartXLower, secondStartXUpper,
        secondStartYLower, secondStartYUpper⟩
    rcases secondFinishBounds with
      ⟨secondFinishXLower, secondFinishXUpper,
        secondFinishYLower, secondFinishYUpper⟩
    rcases normalizedBounds with
      ⟨normalizedXLower, normalizedXUpper,
        normalizedYLower, normalizedYUpper⟩
    rcases normalizedSecond with
        ⟨horizontal, sameY, betweenX⟩ |
        ⟨vertical, sameX, betweenY⟩
    · have horizontalBetween :
          GridSegment.Between
            (second.segment.start.1 +
              drawing.gridSize * reverse.1)
            (second.segment.finish.1 +
              drawing.gridSize * reverse.1)
            normalized.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using betweenX
      have verticalLane :
          normalized.2 =
            second.segment.start.2 +
              drawing.gridSize * reverse.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using sameY
      have horizontalBounds :=
        between_closed_shift_isNeighbor_of_halfOpen_expanded
          periodPositive
          secondStartXLower secondStartXUpper
          secondFinishXLower secondFinishXUpper
          normalizedXLower normalizedXUpper horizontalBetween
      have verticalBounds :=
        lane_shift_isNeighbor_of_halfOpen_expanded
          periodPositive
          secondStartYLower secondStartYUpper
          normalizedYLower normalizedYUpper verticalLane
      exact ⟨by omega, by omega⟩
    · have horizontalLane :
          normalized.1 =
            second.segment.start.1 +
              drawing.gridSize * reverse.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using sameX
      have verticalBetween :
          GridSegment.Between
            (second.segment.start.2 +
              drawing.gridSize * reverse.2)
            (second.segment.finish.2 +
              drawing.gridSize * reverse.2)
            normalized.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using betweenY
      have horizontalBounds :=
        lane_shift_isNeighbor_of_halfOpen_expanded
          periodPositive
          secondStartXLower secondStartXUpper
          normalizedXLower normalizedXUpper horizontalLane
      have verticalBounds :=
        between_closed_shift_isNeighbor_of_halfOpen_expanded
          periodPositive
          secondStartYLower secondStartYUpper
          secondFinishYLower secondFinishYUpper
          normalizedYLower normalizedYUpper verticalBetween
      exact ⟨by omega, by omega⟩
  exact
    (mem_neighborTranslations_iff _).mpr
      (isNeighborTranslation_sub_comm reverseNeighbor)

end PeriodicGridDrawing
end LeanTrominoes
