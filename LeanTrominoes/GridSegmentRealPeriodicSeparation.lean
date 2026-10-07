/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealIntersection

/-! # Closed pieces shorter than one period cannot meet their translated copies -/
namespace LeanTrominoes.GridSegment

theorem normalized_bands_periodic_shifts_unique {period firstLower firstUpper secondLower secondUpper
    firstShift secondShift : Int} (positive : 0 < period)
    (firstNormalized : 0 ≤ firstLower ∧ firstUpper < period)
    (secondNormalized : 0 ≤ secondLower ∧ secondUpper < period) {point : ℝ}
    (firstBounds : (firstLower : ℝ)+(period : ℝ)*firstShift ≤ point ∧
      point ≤ (firstUpper : ℝ)+(period : ℝ)*firstShift)
    (secondBounds : (secondLower : ℝ)+(period : ℝ)*secondShift ≤ point ∧
      point ≤ (secondUpper : ℝ)+(period : ℝ)*secondShift) : firstShift = secondShift := by
  have periodPositive : (0 : ℝ) < period := by exact_mod_cast positive
  have firstLo : (0 : ℝ) ≤ firstLower := by exact_mod_cast firstNormalized.1
  have firstHi : (firstUpper : ℝ) < period := by exact_mod_cast firstNormalized.2
  have secondLo : (0 : ℝ) ≤ secondLower := by exact_mod_cast secondNormalized.1
  have secondHi : (secondUpper : ℝ) < period := by exact_mod_cast secondNormalized.2
  rcases lt_trichotomy firstShift secondShift with less | equal | greater
  · have gap : (firstShift : ℝ)+1 ≤ secondShift := by exact_mod_cast (by omega : firstShift+1 ≤ secondShift)
    have scaled := mul_le_mul_of_nonneg_left gap periodPositive.le
    nlinarith [firstBounds.2,secondBounds.1]
  · exact equal
  · have gap : (secondShift : ℝ)+1 ≤ firstShift := by exact_mod_cast (by omega : secondShift+1 ≤ firstShift)
    have scaled := mul_le_mul_of_nonneg_left gap periodPositive.le
    nlinarith [firstBounds.1,secondBounds.2]

theorem closed_interval_periodic_shifts_unique {period lower upper firstShift secondShift : Int}
    (positive : 0 < period) (span : upper-lower < period) {point : ℝ}
    (firstBounds : (lower : ℝ)+(period : ℝ)*firstShift ≤ point ∧
      point ≤ (upper : ℝ)+(period : ℝ)*firstShift)
    (secondBounds : (lower : ℝ)+(period : ℝ)*secondShift ≤ point ∧
      point ≤ (upper : ℝ)+(period : ℝ)*secondShift) : firstShift = secondShift := by
  have periodPositive : (0 : ℝ) < period := by exact_mod_cast positive
  have width : (upper : ℝ)-lower < period := by exact_mod_cast span
  rcases lt_trichotomy firstShift secondShift with less | equal | greater
  · have gap : (firstShift : ℝ)+1 ≤ secondShift := by exact_mod_cast (by omega : firstShift+1 ≤ secondShift)
    have scaled := mul_le_mul_of_nonneg_left gap periodPositive.le
    nlinarith [firstBounds.2,secondBounds.1]
  · exact equal
  · have gap : (secondShift : ℝ)+1 ≤ firstShift := by exact_mod_cast (by omega : secondShift+1 ≤ firstShift)
    have scaled := mul_le_mul_of_nonneg_left gap periodPositive.le
    nlinarith [firstBounds.1,secondBounds.2]

theorem normalized_bands_disjoint {period firstLower firstUpper secondLower secondUpper firstShift secondShift : Int}
    (positive : 0 < period) (firstNormalized : 0 ≤ firstLower ∧ firstUpper < period)
    (secondNormalized : 0 ≤ secondLower ∧ secondUpper < period)
    (separated : firstUpper < secondLower ∨ secondUpper < firstLower) {point : ℝ}
    (firstBounds : (firstLower : ℝ)+(period : ℝ)*firstShift ≤ point ∧
      point ≤ (firstUpper : ℝ)+(period : ℝ)*firstShift)
    (secondBounds : (secondLower : ℝ)+(period : ℝ)*secondShift ≤ point ∧
      point ≤ (secondUpper : ℝ)+(period : ℝ)*secondShift) : False := by
  have shifts := normalized_bands_periodic_shifts_unique positive firstNormalized secondNormalized firstBounds secondBounds
  rw [shifts] at firstBounds
  rcases separated with before | after
  · have gap : (firstUpper : ℝ) < secondLower := by exact_mod_cast before
    linarith [firstBounds.2,secondBounds.1]
  · have gap : (secondUpper : ℝ) < firstLower := by exact_mod_cast after
    linarith [secondBounds.2,firstBounds.1]

theorem real_translated_copies_disjoint {segment : GridSegment} {period : Int}
    (positive : 0 < period)
    (horizontalSpan : max segment.start.1 segment.finish.1-min segment.start.1 segment.finish.1 < period)
    (verticalSpan : max segment.start.2 segment.finish.2-min segment.start.2 segment.finish.2 < period)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : (segment.translate (Cell.scale period firstCell)).RealContains point)
    (secondContains : (segment.translate (Cell.scale period secondCell)).RealContains point) :
    firstCell = secondCell := by
  have firstBox := realBoxContains_of_realContains firstContains
  have secondBox := realBoxContains_of_realContains secondContains
  simp only [RealBoxContains,translate,Cell.scale,Cell.add,min_add_add_left,max_add_add_left,
    Int.cast_add,Int.cast_mul] at firstBox secondBox
  apply Prod.ext
  · apply closed_interval_periodic_shifts_unique (point := point.1) positive horizontalSpan
    · exact ⟨by linarith [firstBox.1],by linarith [firstBox.2.1]⟩
    · exact ⟨by linarith [secondBox.1],by linarith [secondBox.2.1]⟩
  · apply closed_interval_periodic_shifts_unique (point := point.2) positive verticalSpan
    · exact ⟨by linarith [firstBox.2.2.1],by linarith [firstBox.2.2.2]⟩
    · exact ⟨by linarith [secondBox.2.2.1],by linarith [secondBox.2.2.2]⟩

end LeanTrominoes.GridSegment
