/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealAffineInterpolation

/-! # Strict interpolation between distinct points lies in the parent interior -/
namespace LeanTrominoes.GridSegment

theorem RealContains.interpolate_interior {segment : GridSegment} {first second : ℝ × ℝ}
    (firstContains : segment.RealContains first) (secondContains : segment.RealContains second)
    (different : first ≠ second) {parameter : ℝ} (lower : 0 < parameter) (upper : parameter < 1) :
    segment.RealInteriorContains ((1-parameter)*first.1+parameter*second.1,
      (1-parameter)*first.2+parameter*second.2) := by
  obtain ⟨a,al,au,ax,ay⟩ := firstContains
  obtain ⟨b,bl,bu,bx,byEq⟩ := secondContains
  have parametersDifferent : a ≠ b := by
    intro equal
    apply different
    apply Prod.ext
    · rw [ax,bx,equal]
    · rw [ay,byEq,equal]
  have positiveValue : 0 < a ∨ 0 < b := by
    rcases lt_or_gt_of_ne parametersDifferent with before | after
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  have belowOne : a < 1 ∨ b < 1 := by
    rcases lt_or_gt_of_ne parametersDifferent with before | after
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  refine ⟨(1-parameter)*a+parameter*b,?_,?_,?_,?_⟩
  · rcases positiveValue with firstPositive | secondPositive
    · have positive := mul_pos (by linarith : 0 < 1-parameter) firstPositive
      have nonnegative := mul_nonneg lower.le bl
      linarith
    · have positive := mul_pos lower secondPositive
      have nonnegative := mul_nonneg (by linarith : 0 ≤ 1-parameter) al
      linarith
  · rcases belowOne with firstBelow | secondBelow
    · have positive := mul_pos (by linarith : 0 < 1-parameter) (by linarith : 0 < 1-a)
      have nonnegative := mul_nonneg lower.le (by linarith : 0 ≤ 1-b)
      nlinarith
    · have positive := mul_pos lower (by linarith : 0 < 1-b)
      have nonnegative := mul_nonneg (by linarith : 0 ≤ 1-parameter) (by linarith : 0 ≤ 1-a)
      nlinarith
  · dsimp only [Prod.fst]
    rw [ax,bx]
    ring
  · dsimp only [Prod.snd]
    rw [ay,byEq]
    ring

end LeanTrominoes.GridSegment
