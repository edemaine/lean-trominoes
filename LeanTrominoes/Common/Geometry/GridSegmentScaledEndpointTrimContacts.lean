/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentScaledEndpointTrim

/-! # The trimmed endpoint is the only remaining point in its vertex box -/
namespace LeanTrominoes.GridSegment

theorem trimScaled_source_box_contact {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {lastCut : Int} (cutBound : 0 ≤ lastCut ∧ lastCut ≤ 8) {point : ℝ × ℝ}
    (neighborhood : (32 : ℝ)*segment.start.1-8 ≤ point.1 ∧ point.1 ≤ (32 : ℝ)*segment.start.1+8 ∧
      (32 : ℝ)*segment.start.2-8 ≤ point.2 ∧ point.2 ≤ (32 : ℝ)*segment.start.2+8)
    (contains : (segment.trimScaled 8 lastCut).RealContains point) :
    point = realCell (segment.trimScaled 8 lastCut).start := by
  obtain ⟨t,tLo,tHi,hx,hy⟩ := contains
  have cutLo : (0 : ℝ) ≤ lastCut := by exact_mod_cast cutBound.1
  have cutHi : (lastCut : ℝ) ≤ 8 := by exact_mod_cast cutBound.2
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  cases direction : AxisDirection.between segment.start segment.finish with
  | invalid => simp [direction,AxisDirection.IsGenuine] at genuine
  | east =>
    have coords := (AxisDirection.between_eq_east_iff _ _).mp direction
    have gap : (segment.start.1 : ℝ)+1 ≤ segment.finish.1 := by exact_mod_cast (by omega : segment.start.1+1 ≤ segment.finish.1)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.finish.1 : ℝ)-segment.start.1)-8-lastCut-16 := by linarith
    have tZero : t = 0 := by nlinarith [mul_nonneg tLo slack,neighborhood.2.1]
    rw [tZero] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | north =>
    have coords := (AxisDirection.between_eq_north_iff _ _).mp direction
    have gap : (segment.start.2 : ℝ)+1 ≤ segment.finish.2 := by exact_mod_cast (by omega : segment.start.2+1 ≤ segment.finish.2)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.finish.2 : ℝ)-segment.start.2)-8-lastCut-16 := by linarith
    have tZero : t = 0 := by nlinarith [mul_nonneg tLo slack,neighborhood.2.2.2]
    rw [tZero] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | west =>
    have coords := (AxisDirection.between_eq_west_iff _ _).mp direction
    have gap : (segment.finish.1 : ℝ)+1 ≤ segment.start.1 := by exact_mod_cast (by omega : segment.finish.1+1 ≤ segment.start.1)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.start.1 : ℝ)-segment.finish.1)-8-lastCut-16 := by linarith
    have tZero : t = 0 := by nlinarith [mul_nonneg tLo slack,neighborhood.1]
    rw [tZero] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | south =>
    have coords := (AxisDirection.between_eq_south_iff _ _).mp direction
    have gap : (segment.finish.2 : ℝ)+1 ≤ segment.start.2 := by exact_mod_cast (by omega : segment.finish.2+1 ≤ segment.start.2)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.start.2 : ℝ)-segment.finish.2)-8-lastCut-16 := by linarith
    have tZero : t = 0 := by nlinarith [mul_nonneg tLo slack,neighborhood.2.2.1]
    rw [tZero] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith

theorem trimScaled_target_box_contact {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {firstCut : Int} (cutBound : 0 ≤ firstCut ∧ firstCut ≤ 8) {point : ℝ × ℝ}
    (neighborhood : (32 : ℝ)*segment.finish.1-8 ≤ point.1 ∧ point.1 ≤ (32 : ℝ)*segment.finish.1+8 ∧
      (32 : ℝ)*segment.finish.2-8 ≤ point.2 ∧ point.2 ≤ (32 : ℝ)*segment.finish.2+8)
    (contains : (segment.trimScaled firstCut 8).RealContains point) :
    point = realCell (segment.trimScaled firstCut 8).finish := by
  obtain ⟨t,tLo,tHi,hx,hy⟩ := contains
  have cutLo : (0 : ℝ) ≤ firstCut := by exact_mod_cast cutBound.1
  have cutHi : (firstCut : ℝ) ≤ 8 := by exact_mod_cast cutBound.2
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  cases direction : AxisDirection.between segment.start segment.finish with
  | invalid => simp [direction,AxisDirection.IsGenuine] at genuine
  | east =>
    have coords := (AxisDirection.between_eq_east_iff _ _).mp direction
    have gap : (segment.start.1 : ℝ)+1 ≤ segment.finish.1 := by exact_mod_cast (by omega : segment.start.1+1 ≤ segment.finish.1)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.finish.1 : ℝ)-segment.start.1)-8-firstCut-16 := by linarith
    have tOne : t = 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) slack,neighborhood.1]
    rw [tOne] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | north =>
    have coords := (AxisDirection.between_eq_north_iff _ _).mp direction
    have gap : (segment.start.2 : ℝ)+1 ≤ segment.finish.2 := by exact_mod_cast (by omega : segment.start.2+1 ≤ segment.finish.2)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.finish.2 : ℝ)-segment.start.2)-8-firstCut-16 := by linarith
    have tOne : t = 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) slack,neighborhood.2.2.1]
    rw [tOne] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | west =>
    have coords := (AxisDirection.between_eq_west_iff _ _).mp direction
    have gap : (segment.finish.1 : ℝ)+1 ≤ segment.start.1 := by exact_mod_cast (by omega : segment.finish.1+1 ≤ segment.start.1)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.start.1 : ℝ)-segment.finish.1)-8-firstCut-16 := by linarith
    have tOne : t = 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) slack,neighborhood.2.1]
    rw [tOne] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith
  | south =>
    have coords := (AxisDirection.between_eq_south_iff _ _).mp direction
    have gap : (segment.finish.2 : ℝ)+1 ≤ segment.start.2 := by exact_mod_cast (by omega : segment.finish.2+1 ≤ segment.start.2)
    simp [trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] at hx hy
    have slack : (0 : ℝ) ≤ 32*((segment.start.2 : ℝ)-segment.finish.2)-8-firstCut-16 := by linarith
    have tOne : t = 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) slack,neighborhood.2.2.2]
    rw [tOne] at hx hy
    apply Prod.ext <;> simp [realCell,trimScaled,direction,AxisDirection.step,Cell.scale,Cell.add] <;> nlinarith

end LeanTrominoes.GridSegment
