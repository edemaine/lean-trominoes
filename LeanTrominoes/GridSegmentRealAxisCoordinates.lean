/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry

/-! # Fixed coordinates of real points on orthogonal grid segments -/
namespace LeanTrominoes.GridSegment

theorem realContains_horizontal_y {segment : GridSegment} (horizontal : segment.IsHorizontal)
    {point : ℝ × ℝ} (member : segment.RealContains point) : point.2 = (segment.start.2 : ℝ) := by
  obtain ⟨t,_,_,_,hy⟩ := member
  have equal : (segment.start.2 : ℝ) = segment.finish.2 := by exact_mod_cast horizontal.1
  rw [← equal,sub_self,mul_zero,add_zero] at hy
  exact hy

theorem realContains_vertical_x {segment : GridSegment} (vertical : segment.IsVertical)
    {point : ℝ × ℝ} (member : segment.RealContains point) : point.1 = (segment.start.1 : ℝ) := by
  obtain ⟨t,_,_,hx,_⟩ := member
  have equal : (segment.start.1 : ℝ) = segment.finish.1 := by exact_mod_cast vertical.1
  rw [← equal,sub_self,mul_zero,add_zero] at hx
  exact hx

end LeanTrominoes.GridSegment
