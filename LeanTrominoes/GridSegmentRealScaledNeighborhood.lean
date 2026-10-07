/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealAxisCoordinates
import LeanTrominoes.GridSegmentRealIntersection
import LeanTrominoes.PeriodicGridDrawingScaling

/-! # Small neighborhoods of scaled lattice points avoid nonincident segments -/
namespace LeanTrominoes.GridSegment

private theorem integer_near_scaled_integer {anchor value : Int} {point : ℝ}
    (lower : (32 : ℝ)*anchor-8 ≤ point) (upper : point ≤ (32 : ℝ)*anchor+8)
    (fixed : point = (32 : ℝ)*value) : anchor = value := by
  have lo : 32*anchor-8 ≤ 32*value := by exact_mod_cast (by linarith : (32 : ℝ)*anchor-8 ≤ (32 : ℝ)*value)
  have hi : 32*value ≤ 32*anchor+8 := by exact_mod_cast (by linarith : (32 : ℝ)*value ≤ (32 : ℝ)*anchor+8)
  omega

private theorem between_of_scaled_box {first last anchor : Int} {point : ℝ}
    (pointLower : (min (32*first) (32*last) : Int) ≤ point)
    (pointUpper : point ≤ (max (32*first) (32*last) : Int))
    (anchorLower : (32 : ℝ)*anchor-8 ≤ point) (anchorUpper : point ≤ (32 : ℝ)*anchor+8) :
    Between first last anchor := by
  rcases le_total first last with forward | backward
  · rw [min_eq_left (by omega : 32*first ≤ 32*last)] at pointLower
    rw [max_eq_right (by omega : 32*first ≤ 32*last)] at pointUpper
    push_cast at pointLower pointUpper
    have lo : 32*first ≤ 32*anchor+8 := by exact_mod_cast (by linarith : (32 : ℝ)*first ≤ (32 : ℝ)*anchor+8)
    have hi : 32*anchor-8 ≤ 32*last := by exact_mod_cast (by linarith : (32 : ℝ)*anchor-8 ≤ (32 : ℝ)*last)
    exact Or.inl ⟨by omega,by omega⟩
  · rw [min_eq_right (by omega : 32*last ≤ 32*first)] at pointLower
    rw [max_eq_left (by omega : 32*last ≤ 32*first)] at pointUpper
    push_cast at pointLower pointUpper
    have lo : 32*last ≤ 32*anchor+8 := by exact_mod_cast (by linarith : (32 : ℝ)*last ≤ (32 : ℝ)*anchor+8)
    have hi : 32*anchor-8 ≤ 32*first := by exact_mod_cast (by linarith : (32 : ℝ)*anchor-8 ≤ (32 : ℝ)*first)
    exact Or.inr ⟨by omega,by omega⟩

theorem scaled_neighborhood_contact_implies_incident {segment : GridSegment} (aligned : segment.IsAxisAligned)
    {anchor : Cell} {point : ℝ × ℝ}
    (neighborhood : (32 : ℝ)*anchor.1-8 ≤ point.1 ∧ point.1 ≤ (32 : ℝ)*anchor.1+8 ∧
      (32 : ℝ)*anchor.2-8 ≤ point.2 ∧ point.2 ≤ (32 : ℝ)*anchor.2+8)
    (contains : (segment.scale 32).RealContains point) : segment.Contains anchor := by
  have box := realBoxContains_of_realContains contains
  simp only [RealBoxContains,scale,Cell.scale,Prod.fst,Prod.snd] at box
  rcases aligned with horizontal | vertical
  · have scaledHorizontal : (segment.scale 32).IsHorizontal := by
      constructor
      · change 32*segment.start.2 = 32*segment.finish.2
        rw [horizontal.1]
      · change 32*segment.start.1 ≠ 32*segment.finish.1
        have different := horizontal.2
        omega
    have fixed := realContains_horizontal_y scaledHorizontal contains
    simp only [scale,Cell.scale,Prod.snd,Int.cast_mul,Int.cast_ofNat] at fixed
    exact Or.inl ⟨horizontal,integer_near_scaled_integer neighborhood.2.2.1 neighborhood.2.2.2 fixed,
      between_of_scaled_box box.1 box.2.1 neighborhood.1 neighborhood.2.1⟩
  · have scaledVertical : (segment.scale 32).IsVertical := by
      constructor
      · change 32*segment.start.1 = 32*segment.finish.1
        rw [vertical.1]
      · change 32*segment.start.2 ≠ 32*segment.finish.2
        have different := vertical.2
        omega
    have fixed := realContains_vertical_x scaledVertical contains
    simp only [scale,Cell.scale,Prod.fst,Int.cast_mul,Int.cast_ofNat] at fixed
    exact Or.inr ⟨vertical,integer_near_scaled_integer neighborhood.1 neighborhood.2.1 fixed,
      between_of_scaled_box box.2.2.1 box.2.2.2 neighborhood.2.2.1 neighborhood.2.2.2⟩

end LeanTrominoes.GridSegment
