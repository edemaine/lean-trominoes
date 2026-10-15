/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealGeometry
import Mathlib.Tactic

/-! # Exact rational intersections with vertical integer-grid lines -/
namespace LeanTrominoes.GridSegment

def CrossesVerticalLine (segment : GridSegment) (line : Int) : Prop :=
  (segment.start.1 < line ∧ line < segment.finish.1) ∨
    (segment.finish.1 < line ∧ line < segment.start.1)

instance (segment : GridSegment) (line : Int) : Decidable (segment.CrossesVerticalLine line) := by
  unfold CrossesVerticalLine
  infer_instance

def rationalLineHeight (segment : GridSegment) (line : Int) : ℚ :=
  (segment.start.2 : ℚ)+((line : ℚ)-segment.start.1)*
    ((segment.finish.2 : ℚ)-segment.start.2)/((segment.finish.1 : ℚ)-segment.start.1)

theorem rationalLineHeight_realContains {segment : GridSegment} {line : Int}
    (crosses : segment.CrossesVerticalLine line) :
    segment.RealContains ((line : ℝ),(segment.rationalLineHeight line : ℝ)) := by
  have nonzeroInt : segment.finish.1-segment.start.1 ≠ 0 := by
    rcases crosses with first | second <;> omega
  have nonzero : (segment.finish.1 : ℝ)-segment.start.1 ≠ 0 := by exact_mod_cast nonzeroInt
  let parameter := ((line : ℝ)-segment.start.1)/((segment.finish.1 : ℝ)-segment.start.1)
  have parameterBounds : 0 ≤ parameter ∧ parameter ≤ 1 := by
    rcases crosses with forward | backward
    · have lo : (segment.start.1 : ℝ) < line := by exact_mod_cast forward.1
      have hi : (line : ℝ) < segment.finish.1 := by exact_mod_cast forward.2
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · exact (div_le_one (by linarith : (0 : ℝ) < segment.finish.1-segment.start.1)).mpr (by linarith)
    · have lo : (segment.finish.1 : ℝ) < line := by exact_mod_cast backward.1
      have hi : (line : ℝ) < segment.start.1 := by exact_mod_cast backward.2
      have negativeRatio : parameter = ((segment.start.1 : ℝ)-line)/((segment.start.1 : ℝ)-segment.finish.1) := by
        dsimp [parameter]
        have oppositeNonzero : (segment.start.1 : ℝ)-segment.finish.1 ≠ 0 := by linarith
        field_simp [nonzero,oppositeNonzero] <;> ring
      rw [negativeRatio]
      exact ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith : (0 : ℝ) < segment.start.1-segment.finish.1)).mpr (by linarith)⟩
  refine ⟨parameter,parameterBounds.1,parameterBounds.2,?_,?_⟩
  · dsimp only [Prod.fst,parameter]
    rw [div_mul_cancel₀ _ nonzero]
    ring
  · simp only [rationalLineHeight,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_intCast]
    dsimp only [Prod.snd,parameter]
    ring

theorem rationalLineHeight_not_endpoint {segment : GridSegment} {line : Int}
    (crosses : segment.CrossesVerticalLine line) :
    ((line : ℝ),(segment.rationalLineHeight line : ℝ)) ≠ ((segment.start.1 : ℝ),(segment.start.2 : ℝ)) ∧
      ((line : ℝ),(segment.rationalLineHeight line : ℝ)) ≠ ((segment.finish.1 : ℝ),(segment.finish.2 : ℝ)) := by
  constructor
  · intro equal
    have projected := congrArg Prod.fst equal
    dsimp only [Prod.fst] at projected
    have same : line = segment.start.1 := by exact_mod_cast projected
    rcases crosses with first | second <;> omega
  · intro equal
    have projected := congrArg Prod.fst equal
    dsimp only [Prod.fst] at projected
    have same : line = segment.finish.1 := by exact_mod_cast projected
    rcases crosses with first | second <;> omega

end LeanTrominoes.GridSegment
