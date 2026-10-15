/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisCoordinates
import LeanTrominoes.Common.Geometry.GridSegmentRealIntersection
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingScaling

/-! # A small neighborhood of a scaled integer vertex identifies incidence -/
namespace LeanTrominoes.GridSegment

theorem scaled_integer_near_eq {factor radius anchor value : Int}
    (nonnegative : 0 ≤ radius) (small : radius < factor)
    (near : |(factor : ℝ)*anchor-(factor : ℝ)*value| ≤ radius) : anchor = value := by
  have positive : 0 < factor := by omega
  have bounds := abs_le.mp near
  have lower : -radius ≤ factor*anchor-factor*value := by exact_mod_cast bounds.1
  have upper : factor*anchor-factor*value ≤ radius := by exact_mod_cast bounds.2
  rcases lt_trichotomy anchor value with before | equal | after
  · have gap : anchor+1 ≤ value := by omega
    nlinarith only [gap,lower,small,positive]
  · exact equal
  · have gap : value+1 ≤ anchor := by omega
    nlinarith only [gap,upper,small,positive]

theorem between_of_scaled_neighborhood {factor radius first last anchor : Int} {point : ℝ}
    (nonnegative : 0 ≤ radius) (small : radius < factor)
    (lower : (min (factor*first) (factor*last) : Int) ≤ point)
    (upper : point ≤ (max (factor*first) (factor*last) : Int))
    (near : |point-(factor : ℝ)*anchor| ≤ radius) : Between first last anchor := by
  have positive : 0 < factor := by omega
  have neighborhood := abs_le.mp near
  rcases le_total first last with forward | backward
  · have scaled := mul_le_mul_of_nonneg_left forward positive.le
    rw [min_eq_left scaled] at lower
    rw [max_eq_right scaled] at upper
    have firstBound : factor*first ≤ factor*anchor+radius := by
      have bound : ((factor*first : Int) : ℝ) ≤ (factor*anchor+radius : Int) := by
        push_cast at lower ⊢
        linarith [neighborhood.2]
      exact_mod_cast bound
    have lastBound : factor*anchor-radius ≤ factor*last := by
      have bound : ((factor*anchor-radius : Int) : ℝ) ≤ (factor*last : Int) := by
        push_cast at upper ⊢
        linarith [neighborhood.1]
      exact_mod_cast bound
    refine Or.inl ⟨?_,?_⟩
    · by_contra outside
      have gap : anchor+1 ≤ first := by omega
      nlinarith only [gap,firstBound,small,positive]
    · by_contra outside
      have gap : last+1 ≤ anchor := by omega
      nlinarith only [gap,lastBound,small,positive]
  · have scaled := mul_le_mul_of_nonneg_left backward positive.le
    rw [min_eq_right scaled] at lower
    rw [max_eq_left scaled] at upper
    have lastBound : factor*last ≤ factor*anchor+radius := by
      have bound : ((factor*last : Int) : ℝ) ≤ (factor*anchor+radius : Int) := by
        push_cast at lower ⊢
        linarith [neighborhood.2]
      exact_mod_cast bound
    have firstBound : factor*anchor-radius ≤ factor*first := by
      have bound : ((factor*anchor-radius : Int) : ℝ) ≤ (factor*first : Int) := by
        push_cast at upper ⊢
        linarith [neighborhood.1]
      exact_mod_cast bound
    refine Or.inr ⟨?_,?_⟩
    · by_contra outside
      have gap : anchor+1 ≤ last := by omega
      nlinarith only [gap,lastBound,small,positive]
    · by_contra outside
      have gap : first+1 ≤ anchor := by omega
      nlinarith only [gap,firstBound,small,positive]

theorem scaled_vertical_neighborhood_contact_implies_incident {segment : GridSegment} (vertical : segment.IsVertical)
    {factor radius : Int} (nonnegative : 0 ≤ radius) (small : radius < factor)
    {anchor : Cell} {point : ℝ × ℝ}
    (near : |point.1-(factor : ℝ)*anchor.1| ≤ radius ∧ |point.2-(factor : ℝ)*anchor.2| ≤ radius)
    (contains : (segment.scale factor).RealContains point) : segment.Contains anchor := by
  have positive : 0 < factor := by omega
  have scaledVertical : (segment.scale factor).IsVertical := by
    refine ⟨by simp [scale,Cell.scale,vertical.1],?_⟩
    simp only [scale,Cell.scale]
    exact fun equal => vertical.2 (mul_left_cancel₀ positive.ne' equal)
  have fixed := realContains_vertical_x scaledVertical contains
  simp only [scale,Cell.scale,Int.cast_mul] at fixed
  have anchorX : anchor.1 = segment.start.1 := scaled_integer_near_eq nonnegative small
    (by rw [fixed,abs_sub_comm] at near; exact near.1)
  have box := realBoxContains_of_realContains contains
  simp only [RealBoxContains,scale,Cell.scale] at box
  exact Or.inr ⟨vertical,anchorX,between_of_scaled_neighborhood nonnegative small box.2.2.1 box.2.2.2 near.2⟩

end LeanTrominoes.GridSegment
