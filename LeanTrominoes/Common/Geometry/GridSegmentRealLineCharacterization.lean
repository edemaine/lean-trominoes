/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealIntersection

/-! # Closed straight segments are their supporting line inside their bounding box -/
namespace LeanTrominoes.GridSegment

def RealLineContains (segment : GridSegment) (point : ℝ × ℝ) : Prop :=
  (point.1-segment.start.1)*(segment.finish.2-segment.start.2) =
    (point.2-segment.start.2)*(segment.finish.1-segment.start.1)

private theorem interval_parameter (first last point : ℝ)
    (bounds : min first last ≤ point ∧ point ≤ max first last) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ point = first+t*(last-first) := by
  rcases lt_trichotomy first last with increasing | equal | decreasing
  · have ordered : first ≤ point ∧ point ≤ last := by simpa [increasing.le] using bounds
    refine ⟨(point-first)/(last-first),div_nonneg (by linarith) (by linarith),?_,?_⟩
    · apply (div_le_one (by linarith : 0 < last-first)).mpr
      linarith
    · rw [div_mul_cancel₀ _ (by linarith : last-first ≠ 0)]
      ring
  · refine ⟨0,by norm_num,by norm_num,?_⟩
    subst last
    simp only [min_self,max_self] at bounds
    simp only [zero_mul,add_zero]
    exact le_antisymm bounds.2 bounds.1
  · have ordered : last ≤ point ∧ point ≤ first := by simpa [decreasing.le] using bounds
    refine ⟨(first-point)/(first-last),div_nonneg (by linarith) (by linarith),?_,?_⟩
    · apply (div_le_one (by linarith : 0 < first-last)).mpr
      linarith
    · have cancel := div_mul_cancel₀ (first-point) (by linarith : first-last ≠ 0)
      nlinarith

theorem realContains_iff_box_and_line (segment : GridSegment) (point : ℝ × ℝ) :
    segment.RealContains point ↔ segment.RealBoxContains point ∧ segment.RealLineContains point := by
  constructor
  · intro member
    refine ⟨realBoxContains_of_realContains member,?_⟩
    obtain ⟨t,_,_,hx,hy⟩ := member
    unfold RealLineContains
    rw [hx,hy]
    ring
  · rintro ⟨⟨xlo,xhi,ylo,yhi⟩,line⟩
    unfold RealLineContains at line
    have xbounds : min (segment.start.1 : ℝ) segment.finish.1 ≤ point.1 ∧
        point.1 ≤ max (segment.start.1 : ℝ) segment.finish.1 := by
      simpa only [Int.cast_min,Int.cast_max] using And.intro xlo xhi
    have ybounds : min (segment.start.2 : ℝ) segment.finish.2 ≤ point.2 ∧
        point.2 ≤ max (segment.start.2 : ℝ) segment.finish.2 := by
      simpa only [Int.cast_min,Int.cast_max] using And.intro ylo yhi
    by_cases horizontal : (segment.finish.1 : ℝ)-segment.start.1 = 0
    · have xequal : (segment.start.1 : ℝ) = segment.finish.1 := by linarith
      have pointX : point.1 = segment.start.1 := by
        simp only [xequal,min_self,max_self] at xbounds
        linarith [xbounds.1,xbounds.2]
      obtain ⟨t,lo,hi,hy⟩ := interval_parameter _ _ _ ybounds
      exact ⟨t,lo,hi,by simpa only [horizontal,mul_zero,add_zero] using pointX,hy⟩
    · obtain ⟨t,lo,hi,hx⟩ := interval_parameter _ _ _ xbounds
      refine ⟨t,lo,hi,hx,?_⟩
      have product : ((segment.finish.1 : ℝ)-segment.start.1)*
          (point.2-segment.start.2-t*(segment.finish.2-segment.start.2)) = 0 := by
        rw [hx] at line
        linear_combination -line
      have zero := (mul_eq_zero.mp product).resolve_left horizontal
      linarith

end LeanTrominoes.GridSegment
