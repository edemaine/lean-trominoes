/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentVerticalCore
import LeanTrominoes.GridSegmentRealScaling
import LeanTrominoes.GridSegmentRealInterior

/-! # Every point of a shortened vertical core lies strictly inside its old segment -/
namespace LeanTrominoes.GridSegment

theorem verticalCore_inverse_image_interior {segment : GridSegment} (vertical : segment.IsVertical)
    {factor : Int} {radius : Nat} (positive : 0 < radius) (spacing : 20*(radius : Int) < factor)
    {point : ℝ × ℝ} (contains : (segment.verticalCore factor radius).RealContains point) :
    segment.RealInteriorContains (point.1/(factor : ℝ),point.2/(factor : ℝ)) := by
  have radiusNonnegative : (0 : Int) ≤ radius := by positivity
  have factorPositive : 0 < factor := by omega
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast factorPositive.ne'
  have oldContains := (realContains_scale_inverse segment factorPositive.ne' point).mp
    (verticalCore_realContains_parent vertical spacing contains)
  have recover : ∀ anchor : Cell, (point.1/(factor : ℝ),point.2/(factor : ℝ)) = realCell anchor →
      point = realCell (Cell.scale factor anchor) := by
    intro anchor equal
    have x := congrArg Prod.fst equal
    have y := congrArg Prod.snd equal
    simp only [realCell] at x y
    apply Prod.ext
    all_goals simp only [realCell,Cell.scale,Int.cast_mul]
    · exact (div_eq_iff realNonzero).mp x |>.trans (mul_comm _ _)
    · exact (div_eq_iff realNonzero).mp y |>.trans (mul_comm _ _)
  refine realInteriorContains_of_realContains_of_not_endpoints oldContains ?_ ?_
  · intro equal
    rw [recover segment.start equal] at contains
    exact verticalCore_avoids_scaled_endpoint vertical positive spacing false contains
  · intro equal
    rw [recover segment.finish equal] at contains
    exact verticalCore_avoids_scaled_endpoint vertical positive spacing true contains

end LeanTrominoes.GridSegment
