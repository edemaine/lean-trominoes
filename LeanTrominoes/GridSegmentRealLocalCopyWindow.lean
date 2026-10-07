/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealIntersection

/-! # Only nine copies of a local straight edge can meet the fundamental square -/
namespace LeanTrominoes.GridSegment

theorem real_local_coordinate_copy_window {period source target shift offset : Int} {point : ℝ}
    (positive : 0 < period) (sourceBounds : 0 < source ∧ source < period)
    (targetBounds : 0 < target ∧ target < period) (offsetBounds : -1 ≤ offset ∧ offset ≤ 1)
    (pointBounds : 0 ≤ point ∧ point ≤ (period : ℝ))
    (segmentBounds : ((min (source+period*shift) (target+period*(shift+offset)) : Int) : ℝ) ≤ point ∧
      point ≤ ((max (source+period*shift) (target+period*(shift+offset)) : Int) : ℝ)) : -1 ≤ shift ∧ shift ≤ 1 := by
  constructor
  · by_contra outside
    have sourceShift := mul_le_mul_of_nonneg_left (by omega : shift ≤ -2) positive.le
    have targetShift := mul_le_mul_of_nonneg_left (by omega : shift+offset ≤ -1) positive.le
    have sourceNegative : source+period*shift < 0 := by nlinarith
    have targetNegative : target+period*(shift+offset) < 0 := by nlinarith
    have upperNegative : ((max (source+period*shift) (target+period*(shift+offset)) : Int) : ℝ) < 0 := by
      exact_mod_cast max_lt sourceNegative targetNegative
    linarith [segmentBounds.2,pointBounds.1]
  · by_contra outside
    have sourceShift := mul_le_mul_of_nonneg_left (by omega : 2 ≤ shift) positive.le
    have targetShift := mul_le_mul_of_nonneg_left (by omega : 1 ≤ shift+offset) positive.le
    have sourceLarge : period < source+period*shift := by nlinarith
    have targetLarge : period < target+period*(shift+offset) := by nlinarith
    have lowerLarge : (period : ℝ) < ((min (source+period*shift) (target+period*(shift+offset)) : Int) : ℝ) := by
      exact_mod_cast lt_min sourceLarge targetLarge
    linarith [segmentBounds.1,pointBounds.2]

theorem real_local_segment_copy_window {period : Int} {source target shift offset : Cell} {point : ℝ × ℝ}
    (positive : 0 < period)
    (sourceBounds : 0 < source.1 ∧ source.1 < period ∧ 0 < source.2 ∧ source.2 < period)
    (targetBounds : 0 < target.1 ∧ target.1 < period ∧ 0 < target.2 ∧ target.2 < period)
    (offsetBounds : -1 ≤ offset.1 ∧ offset.1 ≤ 1 ∧ -1 ≤ offset.2 ∧ offset.2 ≤ 1)
    (pointBounds : 0 ≤ point.1 ∧ point.1 ≤ (period : ℝ) ∧ 0 ≤ point.2 ∧ point.2 ≤ (period : ℝ))
    (contains : (GridSegment.mk (Cell.add source (Cell.scale period shift))
      (Cell.add target (Cell.scale period (Cell.add shift offset)))).RealContains point) :
    -1 ≤ shift.1 ∧ shift.1 ≤ 1 ∧ -1 ≤ shift.2 ∧ shift.2 ≤ 1 := by
  have bounds := realBoxContains_of_realContains contains
  simp only [RealBoxContains,Cell.add,Cell.scale] at bounds
  exact ⟨(real_local_coordinate_copy_window (shift := shift.1) positive ⟨sourceBounds.1,sourceBounds.2.1⟩
      ⟨targetBounds.1,targetBounds.2.1⟩ ⟨offsetBounds.1,offsetBounds.2.1⟩ ⟨pointBounds.1,pointBounds.2.1⟩
      ⟨bounds.1,bounds.2.1⟩).1,
    (real_local_coordinate_copy_window (shift := shift.1) positive ⟨sourceBounds.1,sourceBounds.2.1⟩
      ⟨targetBounds.1,targetBounds.2.1⟩ ⟨offsetBounds.1,offsetBounds.2.1⟩ ⟨pointBounds.1,pointBounds.2.1⟩
      ⟨bounds.1,bounds.2.1⟩).2,
    real_local_coordinate_copy_window positive ⟨sourceBounds.2.2.1,sourceBounds.2.2.2⟩
      ⟨targetBounds.2.2.1,targetBounds.2.2.2⟩ ⟨offsetBounds.2.2.1,offsetBounds.2.2.2⟩
      ⟨pointBounds.2.2.1,pointBounds.2.2.2⟩ ⟨bounds.2.2.1,bounds.2.2.2⟩⟩

end LeanTrominoes.GridSegment
