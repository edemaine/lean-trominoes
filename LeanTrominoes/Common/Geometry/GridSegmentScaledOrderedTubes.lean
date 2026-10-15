/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentOrderedLeftRayTubes

/-! # Scaled ordered-core separation independent of route orientation

Only containment in a radius-three tube is needed. Thus the same estimate
applies to translated cores and to cores viewed from their target endpoints.
-/
namespace LeanTrominoes.GridSegment

theorem ordered_right_scaled_tubes_disjoint {first second : GridSegment} {bound factor : Int}
    (boundNonnegative : 0 ≤ bound) (factorPositive : 0 < factor)
    (firstPositive : 0 < first.direction.1) (secondPositive : 0 < second.direction.1)
    (sameColumn : first.start.1 = second.start.1) (ports : first.start.2+2 ≤ second.start.2)
    (ordered : 0 ≤ cross first.direction second.direction) (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 3*(bound+1) < factor) {point : ℝ × ℝ}
    (firstContains : (first.scale factor).RealTubeContains 3 point) :
    ¬(second.scale factor).RealTubeContains 3 point := by
  intro secondContains
  have firstHorizontal : 0 < (first.scale factor).direction.1 := by
    simp only [direction_scale,Cell.scale]
    exact mul_pos factorPositive firstPositive
  have secondHorizontal : 0 < (second.scale factor).direction.1 := by
    simp only [direction_scale,Cell.scale]
    exact mul_pos factorPositive secondPositive
  have scaledColumn : (first.scale factor).start.1 = (second.scale factor).start.1 := by
    simp only [scale,Cell.scale,sameColumn]
  have scaledPorts : ((first.scale factor).start.2 : ℝ)+2*(factor : ℝ) ≤ (second.scale factor).start.2 := by
    have scaled := mul_le_mul_of_nonneg_left ports factorPositive.le
    have scaled' : factor*first.start.2+2*factor ≤ factor*second.start.2 := by nlinarith
    simp only [scale,Cell.scale,Int.cast_mul]
    exact_mod_cast scaled'
  have scaledOrder : 0 ≤ cross (first.scale factor).direction (second.scale factor).direction := by
    rw [cross_scaled_directions]
    exact mul_nonneg (by positivity) ordered
  have scaledSlope : |(second.scale factor).realSlope| ≤ (bound : ℝ) := by
    rw [realSlope_scale second (ne_of_gt factorPositive)]
    exact slopeBound
  have realSpacing : 2*(3 : ℝ)*((bound : ℝ)+1) < 2*(factor : ℝ) := by
    have castSpacing : 3*((bound : ℝ)+1) < factor := by exact_mod_cast spacing
    linarith
  exact ordered_right_tubes_disjoint (by exact_mod_cast boundNonnegative) firstHorizontal secondHorizontal
    scaledColumn scaledPorts scaledOrder scaledSlope realSpacing firstContains secondContains

theorem ordered_left_scaled_tubes_disjoint {first second : GridSegment} {bound factor : Int}
    (boundNonnegative : 0 ≤ bound) (factorPositive : 0 < factor)
    (firstNegative : first.direction.1 < 0) (secondNegative : second.direction.1 < 0)
    (sameColumn : first.start.1 = second.start.1) (ports : first.start.2+2 ≤ second.start.2)
    (ordered : cross first.direction second.direction ≤ 0) (slopeBound : |second.realSlope| ≤ bound)
    (spacing : 3*(bound+1) < factor) {point : ℝ × ℝ}
    (firstContains : (first.scale factor).RealTubeContains 3 point) :
    ¬(second.scale factor).RealTubeContains 3 point := by
  intro secondContains
  have firstHorizontal : (first.scale factor).direction.1 < 0 := by
    simp only [direction_scale,Cell.scale]
    exact mul_neg_of_pos_of_neg factorPositive firstNegative
  have secondHorizontal : (second.scale factor).direction.1 < 0 := by
    simp only [direction_scale,Cell.scale]
    exact mul_neg_of_pos_of_neg factorPositive secondNegative
  have scaledColumn : (first.scale factor).start.1 = (second.scale factor).start.1 := by
    simp only [scale,Cell.scale,sameColumn]
  have scaledPorts : ((first.scale factor).start.2 : ℝ)+2*(factor : ℝ) ≤ (second.scale factor).start.2 := by
    have scaled := mul_le_mul_of_nonneg_left ports factorPositive.le
    have scaled' : factor*first.start.2+2*factor ≤ factor*second.start.2 := by nlinarith
    simp only [scale,Cell.scale,Int.cast_mul]
    exact_mod_cast scaled'
  have scaledOrder : cross (first.scale factor).direction (second.scale factor).direction ≤ 0 := by
    rw [cross_scaled_directions]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ordered
  have scaledSlope : |(second.scale factor).realSlope| ≤ (bound : ℝ) := by
    rw [realSlope_scale second (ne_of_gt factorPositive)]
    exact slopeBound
  have realSpacing : 2*(3 : ℝ)*((bound : ℝ)+1) < 2*(factor : ℝ) := by
    have castSpacing : 3*((bound : ℝ)+1) < factor := by exact_mod_cast spacing
    linarith
  exact ordered_left_tubes_disjoint (by exact_mod_cast boundNonnegative) firstHorizontal secondHorizontal
    scaledColumn scaledPorts scaledOrder scaledSlope realSpacing firstContains secondContains

end LeanTrominoes.GridSegment
