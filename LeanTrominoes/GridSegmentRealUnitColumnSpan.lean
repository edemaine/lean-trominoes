/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalVerticalPerturbation
import LeanTrominoes.GridSegmentRealIntersection

/-! # Integer-endpoint segments meeting a unit column span both rational cuts -/
namespace LeanTrominoes.GridSegment

def SpansUnitColumn (segment : GridSegment) (column : Int) : Prop :=
  (segment.start.1 ≤ column ∧ column+1 ≤ segment.finish.1) ∨
    (segment.finish.1 ≤ column ∧ column+1 ≤ segment.start.1)

theorem unit_column_cut_endpoint_or_crossing {segment : GridSegment} {column : Int}
    (spans : segment.SpansUnitColumn column) (right : Bool) :
    let line := column+if right then 1 else 0
    segment.CrossesVerticalLine line ∨
      (segment.start.1 = line ∧ (if right then segment.finish.1 < line else line < segment.finish.1)) ∨
      (segment.finish.1 = line ∧ (if right then segment.start.1 < line else line < segment.start.1)) := by
  cases right <;> simp only [Bool.false_eq_true,if_false,if_true,add_zero]
  all_goals rcases spans with forward | backward
  all_goals dsimp only [CrossesVerticalLine] <;> omega

theorem realContains_spans_unit_column {segment : GridSegment} {column : Int} {point : ℝ × ℝ}
    (contains : segment.RealContains point) (inside : (column : ℝ) < point.1 ∧ point.1 < (column : ℝ)+1) :
    segment.SpansUnitColumn column := by
  have box := realBoxContains_of_realContains contains
  have lower : min segment.start.1 segment.finish.1 ≤ column := by
    have realBound : ((min segment.start.1 segment.finish.1 : Int) : ℝ) < (column : ℝ)+1 := box.1.trans_lt inside.2
    have integerBound : min segment.start.1 segment.finish.1 < column+1 := by exact_mod_cast realBound
    omega
  have upper : column+1 ≤ max segment.start.1 segment.finish.1 := by
    have realBound : (column : ℝ) < ((max segment.start.1 segment.finish.1 : Int) : ℝ) := inside.1.trans_le box.2.1
    have integerBound : column < max segment.start.1 segment.finish.1 := by exact_mod_cast realBound
    omega
  rcases le_total segment.start.1 segment.finish.1 with forward | backward
  · simp only [min_eq_left forward,max_eq_right forward] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · simp only [min_eq_right backward,max_eq_left backward] at lower upper
    exact Or.inr ⟨lower,upper⟩

theorem rational_unit_column_cut_realInteriorContains {segment : GridSegment} {column : Int} {epsilon : ℚ}
    (spans : segment.SpansUnitColumn column) (positive : 0 < epsilon) (small : epsilon < 1) (right : Bool) :
    segment.RealInteriorContains
      ((((column : ℚ)+(if right then 1-epsilon else epsilon) : ℚ) : ℝ),
        (segment.rationalHeightAt ((column : ℚ)+(if right then 1-epsilon else epsilon)) : ℝ)) := by
  apply rationalHeightAt_realInteriorContains
  have stepPositive : (0 : ℚ) < (if right then 1-epsilon else epsilon) := by cases right <;> simp <;> linarith
  have stepSmall : (if right then 1-epsilon else epsilon) < (1 : ℚ) := by cases right <;> simp <;> linarith
  rcases spans with forward | backward
  · have lo : (segment.start.1 : ℚ) ≤ column := by exact_mod_cast forward.1
    have hi : (column : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast forward.2
    left
    constructor <;> linarith
  · have lo : (segment.finish.1 : ℚ) ≤ column := by exact_mod_cast backward.1
    have hi : (column : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast backward.2
    right
    constructor <;> linarith

theorem unit_column_inner_coordinate_between {segment : GridSegment} {column : Int} {epsilon coordinate : ℚ}
    (spans : segment.SpansUnitColumn column) (positive : 0 < epsilon)
    (bounds : 0 ≤ coordinate ∧ coordinate ≤ 1-2*epsilon) :
    ((segment.start.1 : ℚ) < (column : ℚ)+epsilon+coordinate ∧
      (column : ℚ)+epsilon+coordinate < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < (column : ℚ)+epsilon+coordinate ∧
        (column : ℚ)+epsilon+coordinate < segment.start.1) := by
  rcases spans with forward | backward
  · have lo : (segment.start.1 : ℚ) ≤ column := by exact_mod_cast forward.1
    have hi : (column : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast forward.2
    exact Or.inl ⟨by linarith [bounds.1],by linarith [bounds.2]⟩
  · have lo : (segment.finish.1 : ℚ) ≤ column := by exact_mod_cast backward.1
    have hi : (column : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast backward.2
    exact Or.inr ⟨by linarith [bounds.1],by linarith [bounds.2]⟩

end LeanTrominoes.GridSegment
