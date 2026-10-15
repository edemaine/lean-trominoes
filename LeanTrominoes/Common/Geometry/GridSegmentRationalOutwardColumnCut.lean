/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalPerturbation

/-! # A small column cut meets the interior of an outward incidence segment -/
namespace LeanTrominoes.GridSegment

theorem rationalHeightAt_start (segment : GridSegment) :
    segment.rationalHeightAt segment.start.1 = (segment.start.2 : ℚ) := by
  simp [rationalHeightAt,rationalAbscissaAt,swapAxes]

theorem rationalHeightAt_start_add (segment : GridSegment) (epsilon : ℚ) :
    segment.rationalHeightAt ((segment.start.1 : ℚ)+epsilon) = (segment.start.2 : ℚ)+epsilon*segment.rationalSlope := by
  rw [rationalHeightAt_add,rationalHeightAt_start]

theorem outward_column_cut_realInteriorContains {segment : GridSegment} {epsilon : ℚ}
    (positive : 0 < epsilon) (small : epsilon < 1) (right : Bool)
    (direction : if right then segment.start.1 < segment.finish.1 else segment.finish.1 < segment.start.1) :
    segment.RealInteriorContains
      (((segment.start.1 : ℚ)+(if right then epsilon else -epsilon) : ℝ),
        (segment.rationalHeightAt ((segment.start.1 : ℚ)+(if right then epsilon else -epsilon)) : ℝ)) := by
  have between : ((segment.start.1 : ℚ) < (segment.start.1 : ℚ)+(if right then epsilon else -epsilon) ∧
        (segment.start.1 : ℚ)+(if right then epsilon else -epsilon) < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < (segment.start.1 : ℚ)+(if right then epsilon else -epsilon) ∧
        (segment.start.1 : ℚ)+(if right then epsilon else -epsilon) < segment.start.1) := by
    cases right
    · have dir : segment.finish.1 < segment.start.1 := by simpa using direction
      have step : (segment.finish.1 : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast (by omega : segment.finish.1+1 ≤ segment.start.1)
      right
      constructor <;> simp only [Bool.false_eq_true,↓reduceIte] <;> linarith
    · have dir : segment.start.1 < segment.finish.1 := by simpa using direction
      have step : (segment.start.1 : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast (by omega : segment.start.1+1 ≤ segment.finish.1)
      left
      constructor <;> simp only [↓reduceIte] <;> linarith
  simpa only [Rat.cast_add,Rat.cast_intCast] using rationalHeightAt_realInteriorContains between

end LeanTrominoes.GridSegment
