/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentStraightRayKeys
import LeanTrominoes.Common.Geometry.GridSegmentOrderedRayTubes

/-! # Rational port order is the integer cross-product order -/
namespace LeanTrominoes.GridSegment

theorem straightRayKey_of_right {segment : GridSegment} (right : 0 < segment.direction.1) :
    segment.straightRayKey = .right segment.rationalSlope := by
  have ordered : segment.start.1 < segment.finish.1 := by
    simp only [direction] at right
    omega
  simp only [straightRayKey,ordered,ite_true]

theorem straightRayKey_of_left {segment : GridSegment} (left : segment.direction.1 < 0) :
    segment.straightRayKey = .left segment.rationalSlope := by
  have ordered : segment.finish.1 < segment.start.1 := by
    simp only [direction] at left
    omega
  simp only [straightRayKey,ordered,not_lt_of_ge ordered.le,ite_false,ite_true]

theorem rationalSlope_eq_direction (segment : GridSegment) :
    segment.rationalSlope = (segment.direction.2 : ℚ)/(segment.direction.1 : ℚ) := by
  simp only [rationalSlope,direction,Int.cast_sub]

theorem cross_positive_iff_right_slope_order {first second : GridSegment}
    (firstRight : 0 < first.direction.1) (secondRight : 0 < second.direction.1) :
    0 < cross first.direction second.direction ↔ first.rationalSlope < second.rationalSlope := by
  rw [rationalSlope_eq_direction,rationalSlope_eq_direction,
    div_lt_div_iff₀ (by exact_mod_cast firstRight : (0 : ℚ) < first.direction.1)
      (by exact_mod_cast secondRight : (0 : ℚ) < second.direction.1)]
  have castCross : (cross first.direction second.direction : ℚ) =
      (first.direction.1 : ℚ)*second.direction.2-(first.direction.2 : ℚ)*second.direction.1 := by
    simp only [cross,Int.cast_sub,Int.cast_mul]
  constructor
  · intro positive
    have rationalPositive : (0 : ℚ) < cross first.direction second.direction := by exact_mod_cast positive
    rw [castCross] at rationalPositive
    linarith
  · intro ordered
    have rationalPositive : (0 : ℚ) < cross first.direction second.direction := by rw [castCross]; linarith
    exact_mod_cast rationalPositive

theorem cross_positive_iff_left_slope_order {first second : GridSegment}
    (firstLeft : first.direction.1 < 0) (secondLeft : second.direction.1 < 0) :
    0 < cross first.direction second.direction ↔ first.rationalSlope < second.rationalSlope := by
  have firstDenominator : (0 : ℚ) < -(first.direction.1 : ℚ) := by exact_mod_cast (neg_pos.mpr firstLeft)
  have secondDenominator : (0 : ℚ) < -(second.direction.1 : ℚ) := by exact_mod_cast (neg_pos.mpr secondLeft)
  rw [rationalSlope_eq_direction,rationalSlope_eq_direction,
    ← neg_div_neg_eq (first.direction.2 : ℚ) (first.direction.1 : ℚ),
    ← neg_div_neg_eq (second.direction.2 : ℚ) (second.direction.1 : ℚ),
    div_lt_div_iff₀ firstDenominator secondDenominator]
  simp only [neg_mul_neg]
  have castCross : (cross first.direction second.direction : ℚ) =
      (first.direction.1 : ℚ)*second.direction.2-(first.direction.2 : ℚ)*second.direction.1 := by
    simp only [cross,Int.cast_sub,Int.cast_mul]
  constructor
  · intro positive
    have rationalPositive : (0 : ℚ) < cross first.direction second.direction := by exact_mod_cast positive
    rw [castCross] at rationalPositive
    linarith
  · intro ordered
    have rationalPositive : (0 : ℚ) < cross first.direction second.direction := by rw [castCross]; linarith
    exact_mod_cast rationalPositive

end LeanTrominoes.GridSegment
