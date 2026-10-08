/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalVerticalPerturbation

/-! # Reversing a nonvertical segment preserves its exact line height -/
namespace LeanTrominoes.GridSegment

theorem rationalHeightAt_reverse {segment : GridSegment} (nonvertical : segment.start.1 ≠ segment.finish.1) (coordinate : ℚ) :
    segment.reverse.rationalHeightAt coordinate = segment.rationalHeightAt coordinate := by
  have different : (segment.start.1 : ℚ) ≠ segment.finish.1 := by exact_mod_cast nonvertical
  have forward : (segment.finish.1 : ℚ)-segment.start.1 ≠ 0 := sub_ne_zero.mpr different.symm
  have backward : (segment.start.1 : ℚ)-segment.finish.1 ≠ 0 := sub_ne_zero.mpr different
  unfold rationalHeightAt rationalAbscissaAt swapAxes reverse
  dsimp only [Prod.swap,Prod.fst,Prod.snd]
  field_simp [forward,backward]
  <;> ring

end LeanTrominoes.GridSegment
