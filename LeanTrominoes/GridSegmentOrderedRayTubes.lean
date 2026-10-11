/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealTube

/-! # Tube separation for ordered rays leaving a common vertical side

Incident edges need a different estimate from disjoint input segments.
Distinct ports and ordered slopes provide a vertical gap independent of the
lengths of the core segments. A refinement linear in the slope bound is
enough to protect that gap during rasterization.
-/
namespace LeanTrominoes.GridSegment

noncomputable def realSlope (segment : GridSegment) : ℝ :=
  (segment.direction.2 : ℝ)/(segment.direction.1 : ℝ)

theorem realContains_lineHeight {segment : GridSegment} (horizontal : segment.direction.1 ≠ 0)
    {point : ℝ × ℝ} (contains : segment.RealContains point) :
    point.2 = (segment.start.2 : ℝ)+segment.realSlope*(point.1-segment.start.1) := by
  obtain ⟨t,_,_,hx,hy⟩ := contains
  have nonzero : (segment.direction.1 : ℝ) ≠ 0 := by exact_mod_cast horizontal
  rw [hx,hy]
  simp only [realSlope,direction,Int.cast_sub] at nonzero ⊢
  field_simp
  ring

theorem realSlope_le_of_cross_nonnegative {first second : GridSegment}
    (firstPositive : 0 < first.direction.1) (secondPositive : 0 < second.direction.1)
    (ordered : 0 ≤ cross first.direction second.direction) : first.realSlope ≤ second.realSlope := by
  have firstRealPositive : (0 : ℝ) < first.direction.1 := by exact_mod_cast firstPositive
  have secondRealPositive : (0 : ℝ) < second.direction.1 := by exact_mod_cast secondPositive
  unfold realSlope
  apply (div_le_div_iff₀ firstRealPositive secondRealPositive).mpr
  have realOrdered : (0 : ℝ) ≤ (first.direction.1 : ℝ)*second.direction.2-
      (first.direction.2 : ℝ)*second.direction.1 := by exact_mod_cast ordered
  linarith

theorem ordered_right_tubes_disjoint {first second : GridSegment} {bound gap radius : ℝ}
    (boundNonnegative : 0 ≤ bound)
    (firstPositive : 0 < first.direction.1) (secondPositive : 0 < second.direction.1)
    (sameColumn : first.start.1 = second.start.1)
    (ports : (first.start.2 : ℝ)+gap ≤ second.start.2)
    (ordered : 0 ≤ cross first.direction second.direction)
    (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 2*radius*(bound+1) < gap)
    {point : ℝ × ℝ} (firstContains : first.RealTubeContains radius point) :
    ¬second.RealTubeContains radius point := by
  rintro ⟨secondPoint,secondContains,secondNearX,secondNearY⟩
  obtain ⟨firstPoint,firstContains,firstNearX,firstNearY⟩ := firstContains
  have firstHeight := realContains_lineHeight (ne_of_gt firstPositive) firstContains
  have secondHeight := realContains_lineHeight (ne_of_gt secondPositive) secondContains
  have slopes := realSlope_le_of_cross_nonnegative firstPositive secondPositive ordered
  have firstForward : (first.start.1 : ℝ) ≤ firstPoint.1 := by
    obtain ⟨t,lower,_,x,_⟩ := firstContains
    have positive : (0 : ℝ) ≤ (first.finish.1 : ℝ)-first.start.1 := by
      exact_mod_cast firstPositive.le
    nlinarith [mul_nonneg lower positive]
  have nearX : |secondPoint.1-firstPoint.1| ≤ 2*radius := by
    have firstNear := abs_le.mp firstNearX
    have secondNear := abs_le.mp secondNearX
    rw [abs_le]
    constructor <;> linarith
  have nearY : |secondPoint.2-firstPoint.2| ≤ 2*radius := by
    have firstNear := abs_le.mp firstNearY
    have secondNear := abs_le.mp secondNearY
    rw [abs_le]
    constructor <;> linarith
  have slopeError : |second.realSlope*(secondPoint.1-firstPoint.1)| ≤ bound*(2*radius) := by
    rw [abs_mul]
    exact mul_le_mul slopeBound nearX (abs_nonneg _) boundNonnegative
  have orderedOffset := mul_nonneg (sub_nonneg.mpr slopes) (sub_nonneg.mpr firstForward)
  rw [← sameColumn] at secondHeight
  have errorLower := (abs_le.mp slopeError).1
  have heightUpper := (abs_le.mp nearY).2
  nlinarith

end LeanTrominoes.GridSegment
