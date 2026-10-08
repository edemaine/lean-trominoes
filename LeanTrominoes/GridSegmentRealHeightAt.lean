/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalVerticalPerturbation

/-! # A real contact lies on the line specified by its exact rational height -/
namespace LeanTrominoes.GridSegment

theorem realContains_affine_height {segment : GridSegment} (nonvertical : segment.start.1 ≠ segment.finish.1)
    (coordinate : ℚ) {point : ℝ × ℝ} (contains : segment.RealContains point) :
    point.2 = (segment.rationalHeightAt coordinate : ℝ)+(segment.rationalSlope : ℝ)*(point.1-(coordinate : ℝ)) := by
  obtain ⟨t,_,_,hx,hy⟩ := contains
  have nonzero : (segment.finish.1 : ℝ)-segment.start.1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast nonvertical.symm)
  unfold rationalHeightAt rationalAbscissaAt rationalSlope swapAxes
  dsimp only [Prod.swap,Prod.fst,Prod.snd]
  push_cast
  rw [hx,hy]
  field_simp [nonzero]
  ring

end LeanTrominoes.GridSegment
