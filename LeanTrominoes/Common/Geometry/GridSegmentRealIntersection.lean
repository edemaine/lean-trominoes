/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealGeometry

/-! # A real intersection of orthogonal grid segments has an integer witness -/
namespace LeanTrominoes.GridSegment

def RealBoxContains (segment : GridSegment) (point : ℝ × ℝ) : Prop :=
  (min segment.start.1 segment.finish.1 : Int) ≤ point.1 ∧
    point.1 ≤ (max segment.start.1 segment.finish.1 : Int) ∧
    (min segment.start.2 segment.finish.2 : Int) ≤ point.2 ∧
    point.2 ≤ (max segment.start.2 segment.finish.2 : Int)

private theorem convex_bounds (first last : Int) (t point : ℝ) (lo : 0 ≤ t) (hi : t ≤ 1)
    (value : point = first+t*(last-first)) :
    (min first last : Int) ≤ point ∧ point ≤ (max first last : Int) := by
  rcases le_total first last with increasing | decreasing
  · rw [min_eq_left increasing,max_eq_right increasing]
    have positive : (0 : ℝ) ≤ (last : ℝ)-first := by exact_mod_cast sub_nonneg.mpr increasing
    constructor <;> nlinarith [mul_nonneg lo positive,mul_nonneg (by linarith : 0 ≤ 1-t) positive]
  · rw [min_eq_right decreasing,max_eq_left decreasing]
    have positive : (0 : ℝ) ≤ (first : ℝ)-last := by exact_mod_cast sub_nonneg.mpr decreasing
    constructor <;> nlinarith [mul_nonneg lo positive,mul_nonneg (by linarith : 0 ≤ 1-t) positive]

theorem realBoxContains_of_realContains {segment : GridSegment} {point : ℝ × ℝ}
    (member : segment.RealContains point) : segment.RealBoxContains point := by
  obtain ⟨t,lo,hi,hx,hy⟩ := member
  exact ⟨(convex_bounds _ _ t _ lo hi hx).1,(convex_bounds _ _ t _ lo hi hx).2,
    (convex_bounds _ _ t _ lo hi hy).1,(convex_bounds _ _ t _ lo hi hy).2⟩

private theorem between_of_min_max {first last point : Int}
    (lo : min first last ≤ point) (hi : point ≤ max first last) : Between first last point := by
  unfold Between
  rcases le_total first last with increasing | decreasing
  · left
    rw [min_eq_left increasing] at lo
    rw [max_eq_right increasing] at hi
    exact ⟨lo,hi⟩
  · right
    rw [min_eq_right decreasing] at lo
    rw [max_eq_left decreasing] at hi
    exact ⟨lo,hi⟩

theorem contains_of_realBoxContains_of_isAxisAligned {segment : GridSegment} {point : Cell}
    (aligned : segment.IsAxisAligned)
    (member : segment.RealBoxContains ((point.1 : ℝ),(point.2 : ℝ))) : segment.Contains point := by
  obtain ⟨xlo,xhi,ylo,yhi⟩ := member
  simp only [Prod.fst,Prod.snd] at xlo xhi ylo yhi
  have xl : min segment.start.1 segment.finish.1 ≤ point.1 := by exact_mod_cast xlo
  have xh : point.1 ≤ max segment.start.1 segment.finish.1 := by exact_mod_cast xhi
  have yl : min segment.start.2 segment.finish.2 ≤ point.2 := by exact_mod_cast ylo
  have yh : point.2 ≤ max segment.start.2 segment.finish.2 := by exact_mod_cast yhi
  rcases aligned with horizontal | vertical
  · refine Or.inl ⟨horizontal,?_,between_of_min_max xl xh⟩
    have equal := horizontal.1
    rw [horizontal.1] at yl yh
    simp only [min_self,max_self] at yl yh
    omega
  · refine Or.inr ⟨vertical,?_,between_of_min_max yl yh⟩
    have equal := vertical.1
    rw [vertical.1] at xl xh
    simp only [min_self,max_self] at xl xh
    omega

theorem real_intersection_has_integer_witness {first second : GridSegment} {point : ℝ × ℝ}
    (firstAxis : first.IsAxisAligned) (secondAxis : second.IsAxisAligned)
    (firstMember : first.RealContains point) (secondMember : second.RealContains point) :
    ∃ witness : Cell, first.Contains witness ∧ second.Contains witness := by
  have firstBox := realBoxContains_of_realContains firstMember
  have secondBox := realBoxContains_of_realContains secondMember
  let x := max (min first.start.1 first.finish.1) (min second.start.1 second.finish.1)
  let y := max (min first.start.2 first.finish.2) (min second.start.2 second.finish.2)
  have xFirst : x ≤ max first.start.1 first.finish.1 := by
    apply max_le
    · exact_mod_cast (le_trans firstBox.1 firstBox.2.1)
    · exact_mod_cast (le_trans secondBox.1 firstBox.2.1)
  have xSecond : x ≤ max second.start.1 second.finish.1 := by
    apply max_le
    · exact_mod_cast (le_trans firstBox.1 secondBox.2.1)
    · exact_mod_cast (le_trans secondBox.1 secondBox.2.1)
  have yFirst : y ≤ max first.start.2 first.finish.2 := by
    apply max_le
    · exact_mod_cast (le_trans firstBox.2.2.1 firstBox.2.2.2)
    · exact_mod_cast (le_trans secondBox.2.2.1 firstBox.2.2.2)
  have ySecond : y ≤ max second.start.2 second.finish.2 := by
    apply max_le
    · exact_mod_cast (le_trans firstBox.2.2.1 secondBox.2.2.2)
    · exact_mod_cast (le_trans secondBox.2.2.1 secondBox.2.2.2)
  refine ⟨(x,y),contains_of_realBoxContains_of_isAxisAligned firstAxis ?_,
    contains_of_realBoxContains_of_isAxisAligned secondAxis ?_⟩
  · change (_ : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (_ : ℝ) ∧
      (_ : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (_ : ℝ)
    exact ⟨by exact_mod_cast (le_max_left (min first.start.1 first.finish.1) (min second.start.1 second.finish.1)),by exact_mod_cast xFirst,
      by exact_mod_cast (le_max_left (min first.start.2 first.finish.2) (min second.start.2 second.finish.2)),by exact_mod_cast yFirst⟩
  · change (_ : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (_ : ℝ) ∧
      (_ : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (_ : ℝ)
    exact ⟨by exact_mod_cast (le_max_right (min first.start.1 first.finish.1) (min second.start.1 second.finish.1)),by exact_mod_cast xSecond,
      by exact_mod_cast (le_max_right (min first.start.2 first.finish.2) (min second.start.2 second.finish.2)),by exact_mod_cast ySecond⟩

end LeanTrominoes.GridSegment
