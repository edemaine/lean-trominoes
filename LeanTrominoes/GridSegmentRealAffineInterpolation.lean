/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry
import Mathlib.Tactic

/-! # A closed real segment contains every affine interpolation of its points -/
namespace LeanTrominoes.GridSegment

theorem RealContains.interpolate {segment : GridSegment} {first second : ℝ × ℝ}
    (firstContains : segment.RealContains first) (secondContains : segment.RealContains second)
    {parameter : ℝ} (lower : 0 ≤ parameter) (upper : parameter ≤ 1) :
    segment.RealContains ((1-parameter)*first.1+parameter*second.1,
      (1-parameter)*first.2+parameter*second.2) := by
  obtain ⟨a,al,au,ax,ay⟩ := firstContains
  obtain ⟨b,bl,bu,bx,byEq⟩ := secondContains
  refine ⟨(1-parameter)*a+parameter*b,
    add_nonneg (mul_nonneg (by linarith) al) (mul_nonneg lower bl),?_,?_,?_⟩
  · calc
      (1-parameter)*a+parameter*b ≤ (1-parameter)*1+parameter*1 :=
        add_le_add (mul_le_mul_of_nonneg_left au (by linarith)) (mul_le_mul_of_nonneg_left bu lower)
      _ = 1 := by ring
  · dsimp only [Prod.fst]
    rw [ax,bx]
    ring
  · dsimp only [Prod.snd]
    rw [ay,byEq]
    ring

end LeanTrominoes.GridSegment
