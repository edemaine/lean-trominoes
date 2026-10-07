/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry
import LeanTrominoes.PeriodicGridDrawingScaling

/-! # Uniform scaling of real segment images -/
namespace LeanTrominoes.GridSegment

theorem realContains_scale (segment : GridSegment) {factor : Int} (nonzero : factor ≠ 0) (point : ℝ × ℝ) :
    (segment.scale factor).RealContains ((factor : ℝ)*point.1,(factor : ℝ)*point.2) ↔
      segment.RealContains point := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  unfold RealContains scale
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul]
  constructor
  · rintro ⟨t,lo,hi,hx,hy⟩
    refine ⟨t,lo,hi,?_,?_⟩
    · apply mul_left_cancel₀ realNonzero
      calc (factor : ℝ)*point.1 = _ := hx
           _ = (factor : ℝ)*((segment.start.1 : ℝ)+t*(segment.finish.1-segment.start.1)) := by ring
    · apply mul_left_cancel₀ realNonzero
      calc (factor : ℝ)*point.2 = _ := hy
           _ = (factor : ℝ)*((segment.start.2 : ℝ)+t*(segment.finish.2-segment.start.2)) := by ring
  · rintro ⟨t,lo,hi,hx,hy⟩
    refine ⟨t,lo,hi,?_,?_⟩
    · rw [hx]
      ring
    · rw [hy]
      ring

theorem realContains_scale_inverse (segment : GridSegment) {factor : Int} (nonzero : factor ≠ 0) (point : ℝ × ℝ) :
    (segment.scale factor).RealContains point ↔
      segment.RealContains (point.1/(factor : ℝ),point.2/(factor : ℝ)) := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  simpa only [mul_div_cancel₀ _ realNonzero,Prod.mk.eta] using
    realContains_scale segment nonzero (point.1/(factor : ℝ),point.2/(factor : ℝ))

end LeanTrominoes.GridSegment
