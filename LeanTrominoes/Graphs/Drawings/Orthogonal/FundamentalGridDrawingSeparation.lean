/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingFiniteContinuousPlanarity

/-! # Contacts between strictly contained periodic copies have zero relative translation -/
namespace LeanTrominoes.PeriodicOrthocrossing
theorem finite_lane_shift_zero
    {period base shift point : Int}
    (periodPositive : 0 < period)
    (baseLower : 0 ≤ base)
    (baseUpper : base < period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (equal : point = base + period * shift) :
    shift = 0 := by
  have notTooLow : ¬shift ≤ -1 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -1 * period := by
      nlinarith
    omega
  have notTooHigh : ¬1 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : period ≤ period * shift := by
      nlinarith
    omega
  omega

/-- The same neighboring-translation bound holds when the canonical point
lies strictly between two translated expanded-square coordinates. -/
theorem finite_between_shift_zero
    {period first last shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : 0 ≤ first)
    (firstUpper : first < period)
    (lastLower : 0 ≤ last)
    (lastUpper : last < period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (between :
      GridSegment.StrictlyBetween
        (first + period * shift)
        (last + period * shift) point) :
    shift = 0 := by
  have notTooLow : ¬shift ≤ -1 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -1 * period := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;>
      omega
  have notTooHigh : ¬1 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : period ≤ period * shift := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;>
      omega
  omega

theorem finite_overlap_shift_zero
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
    shift = 0 := by
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
  have notTooLow : ¬shift ≤ -1 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -1 * period := by
      nlinarith
    omega
  have notTooHigh : ¬1 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 1) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        period ≤ period * shift := by
      nlinarith
    omega
  omega

end LeanTrominoes.PeriodicOrthocrossing
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing
theorem occurrence_translate_eq_zero_of_contact
    {drawing : PeriodicGridDrawing} {segment : GridSegment}
    (bounds : drawing.PositionInFundamentalSquare segment.start ∧
      drawing.PositionInFundamentalSquare segment.finish)
    {translate point : Cell} (pointBounds : drawing.PositionInFundamentalSquare point)
    (contains : (segment.translate (drawing.periodTranslation translate)).InteriorContains point) :
    translate=(0,0) := by
  have periodPositive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have translateZero : translate.1=0 ∧ translate.2=0 := by
    rcases bounds with ⟨startBounds, finishBounds⟩
    rcases startBounds with
      ⟨startXLower, startXUpper, startYLower, startYUpper⟩
    rcases finishBounds with
      ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
    rcases pointBounds with
      ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
    rcases contains with
      ⟨horizontal, same, between⟩ |
        ⟨vertical, same, between⟩
    · have same' :
          point.2 =
            segment.start.2 +
              drawing.gridSize * translate.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using same
      have between' :
          GridSegment.StrictlyBetween
            (segment.start.1 +
              drawing.gridSize * translate.1)
            (segment.finish.1 +
              drawing.gridSize * translate.1)
            point.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using between
      exact
        ⟨finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            (le_of_lt pointXLower) pointXUpper between',
          finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            (le_of_lt pointYLower) pointYUpper same'⟩
    · have same' :
          point.1 =
            segment.start.1 +
              drawing.gridSize * translate.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using same
      have between' :
          GridSegment.StrictlyBetween
            (segment.start.2 +
              drawing.gridSize * translate.2)
            (segment.finish.2 +
              drawing.gridSize * translate.2)
            point.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using between
      exact
        ⟨finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            (le_of_lt pointXLower) pointXUpper same',
          finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            (le_of_lt pointYLower) pointYUpper between'⟩
  exact Prod.ext translateZero.1 translateZero.2

theorem relativeTranslate_eq_zero_of_contact
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (first.segment.translate
        (drawing.periodTranslation firstTranslate)).InteriorContains point)
    (secondContains :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).Contains point) :
    Cell.sub firstTranslate secondTranslate = (0,0) := by
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedFundamental :
      normalized ∈ drawing.fundamentalPoints :=
    fundamental_of_contains
      (endpointBounds second secondMember).1
      (endpointBounds second secondMember).2
      normalizedSecond
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := endpointBounds first firstMember
  have normalizedBounds :=
    (mem_fundamentalPoints_iff drawing normalized).mp
      normalizedFundamental
  have relativeZero : relative.1=0 ∧ relative.2=0 := by
    rcases firstBounds with ⟨startBounds, finishBounds⟩
    rcases startBounds with
      ⟨startXLower, startXUpper, startYLower, startYUpper⟩
    rcases finishBounds with
      ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
    rcases normalizedBounds with
      ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
    rcases normalizedFirst with
      ⟨horizontal, same, between⟩ |
        ⟨vertical, same, between⟩
    · have same' :
          normalized.2 =
            first.segment.start.2 +
              drawing.gridSize * relative.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using same
      have between' :
          GridSegment.StrictlyBetween
            (first.segment.start.1 +
              drawing.gridSize * relative.1)
            (first.segment.finish.1 +
              drawing.gridSize * relative.1)
            normalized.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using between
      exact
        ⟨finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            pointXLower pointXUpper between',
          finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            pointYLower pointYUpper same'⟩
    · have same' :
          normalized.1 =
            first.segment.start.1 +
              drawing.gridSize * relative.1 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using same
      have between' :
          GridSegment.StrictlyBetween
            (first.segment.start.2 +
              drawing.gridSize * relative.2)
            (first.segment.finish.2 +
              drawing.gridSize * relative.2)
            normalized.2 := by
        simpa [GridSegment.translate, periodTranslation,
          Cell.add, Cell.scale, add_comm] using between
      exact
        ⟨finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            pointXLower pointXUpper same',
          finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            pointYLower pointYUpper between'⟩
  exact Prod.ext relativeZero.1 relativeZero.2

theorem relativeTranslate_eq_zero_of_interiorsMeet
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
    Cell.sub firstTranslate secondTranslate = (0,0) := by
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
  have relativeZero : relative.1=0 ∧ relative.2=0 := by
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
        ⟨finite_overlap_shift_zero periodPositive
            firstStartXLower firstStartXUpper
            firstFinishXLower firstFinishXUpper
            secondStartXLower secondStartXUpper
            secondFinishXLower secondFinishXUpper overlap,
          finite_lane_shift_zero periodPositive
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
        ⟨finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            (by omega) (by omega) lane,
          finite_overlap_shift_zero periodPositive
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
        ⟨finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) horizontalBetween,
          finite_lane_shift_zero periodPositive
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
        ⟨finite_lane_shift_zero periodPositive
            (by omega) (by omega)
            translatedXLower translatedXUpper rfl,
          finite_between_shift_zero periodPositive
            (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) verticalBetween⟩
  exact Prod.ext relativeZero.1 relativeZero.2

end LeanTrominoes.PeriodicGridDrawing
