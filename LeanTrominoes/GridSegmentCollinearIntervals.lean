/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentSeparatingAxes

/-! # Collinear point membership reduces to one nonconstant coordinate -/
namespace LeanTrominoes.GridSegment

private theorem intervalParameter (first last value : ℝ)
    (bounds : min first last≤value ∧ value≤max first last) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧ value=first+t*(last-first) := by
  rcases lt_trichotomy first last with increasing | equal | decreasing
  · have ordered : first≤value ∧ value≤last := by simpa [increasing.le] using bounds
    refine ⟨(value-first)/(last-first),div_nonneg (by linarith) (by linarith),?_,?_⟩
    · apply (div_le_one (by linarith : 0<last-first)).mpr
      linarith
    · rw [div_mul_cancel₀ _ (by linarith : last-first≠0)]
      ring
  · subst last
    refine ⟨0,by norm_num,by norm_num,?_⟩
    simp only [min_self,max_self] at bounds
    simp only [zero_mul,add_zero]
    exact le_antisymm bounds.2 bounds.1
  · have ordered : last≤value ∧ value≤first := by simpa [decreasing.le] using bounds
    refine ⟨(first-value)/(first-last),div_nonneg (by linarith) (by linarith),?_,?_⟩
    · apply (div_le_one (by linarith : 0<first-last)).mpr
      linarith
    · have cancel := div_mul_cancel₀ (first-value) (by linarith : first-last≠0)
      nlinarith

theorem realContains_of_collinear_x {s : GridSegment} {p : Cell} (nonzero : s.direction.1≠0)
    (collinear : s.side p=0)
    (bounds : min s.start.1 s.finish.1≤p.1 ∧ p.1≤max s.start.1 s.finish.1) :
    s.RealContains ((p.1:ℝ),(p.2:ℝ)) := by
  have xBounds : min (s.start.1:ℝ) s.finish.1≤(p.1:ℝ) ∧ (p.1:ℝ)≤max (s.start.1:ℝ) s.finish.1 := by
    exact_mod_cast bounds
  obtain ⟨t,lo,hi,x⟩ := intervalParameter _ _ _ xBounds
  have line : ((s.finish.1:ℝ)-s.start.1)*((p.2:ℝ)-s.start.2) -
      ((s.finish.2:ℝ)-s.start.2)*((p.1:ℝ)-s.start.1)=0 := by
    exact_mod_cast collinear
  have dxNonzero : (s.finish.1:ℝ)-s.start.1≠0 := by exact_mod_cast nonzero
  have product : ((s.finish.1:ℝ)-s.start.1)*
      ((p.2:ℝ)-s.start.2-t*((s.finish.2:ℝ)-s.start.2))=0 := by
    rw [x] at line
    linear_combination line
  have y := (mul_eq_zero.mp product).resolve_left dxNonzero
  exact ⟨t,lo,hi,x,by linarith⟩

theorem realContains_of_collinear_y {s : GridSegment} {p : Cell} (nonzero : s.direction.2≠0)
    (collinear : s.side p=0)
    (bounds : min s.start.2 s.finish.2≤p.2 ∧ p.2≤max s.start.2 s.finish.2) :
    s.RealContains ((p.1:ℝ),(p.2:ℝ)) := by
  have yBounds : min (s.start.2:ℝ) s.finish.2≤(p.2:ℝ) ∧ (p.2:ℝ)≤max (s.start.2:ℝ) s.finish.2 := by
    exact_mod_cast bounds
  obtain ⟨t,lo,hi,y⟩ := intervalParameter _ _ _ yBounds
  have line : ((s.finish.1:ℝ)-s.start.1)*((p.2:ℝ)-s.start.2) -
      ((s.finish.2:ℝ)-s.start.2)*((p.1:ℝ)-s.start.1)=0 := by
    exact_mod_cast collinear
  have dyNonzero : (s.finish.2:ℝ)-s.start.2≠0 := by exact_mod_cast nonzero
  have product : ((s.finish.2:ℝ)-s.start.2)*
      ((p.1:ℝ)-s.start.1-t*((s.finish.1:ℝ)-s.start.1))=0 := by
    rw [y] at line
    linear_combination -line
  have x := (mul_eq_zero.mp product).resolve_left dyNonzero
  exact ⟨t,lo,hi,by linarith,y⟩

theorem strictlySeparated_x {first second : GridSegment}
    (gap : max first.start.1 first.finish.1<min second.start.1 second.finish.1) :
    StrictlySeparated (1,0) first second := by
  unfold StrictlySeparated linearForm
  simp only [one_mul,zero_mul,add_zero]
  omega

theorem strictlySeparated_y {first second : GridSegment}
    (gap : max first.start.2 first.finish.2<min second.start.2 second.finish.2) :
    StrictlySeparated (0,1) first second := by
  unfold StrictlySeparated linearForm
  simp only [one_mul,zero_mul,zero_add]
  omega

end LeanTrominoes.GridSegment
