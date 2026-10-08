/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalVerticalPerturbation
import LeanTrominoes.RealRectangleBoundaryUniqueSides

/-! # Exact height of a rational proper contact on a nonvertical segment -/
namespace LeanTrominoes.GridSegment

theorem rationalHeightAt_eq_of_realContains {segment : GridSegment} {coordinate height : ℚ}
    (between : ((segment.start.1 : ℚ) < coordinate ∧ coordinate < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < coordinate ∧ coordinate < segment.start.1))
    (contains : segment.RealContains ((coordinate : ℝ),(height : ℝ))) : segment.rationalHeightAt coordinate = height := by
  have proper := rationalHeightAt_realInteriorContains between
  have away : (segment.start.1 : ℝ) ≠ (coordinate : ℝ) := by
    rcases between with forward | backward
    · exact ne_of_lt (by exact_mod_cast forward.1)
    · exact ne_of_gt (by exact_mod_cast backward.2)
  have equal := realContains_eq_of_same_x (realInteriorContains_implies_realContains proper) contains rfl away
  have equalY := congrArg Prod.snd equal
  dsimp only at equalY
  exact_mod_cast equalY

end LeanTrominoes.GridSegment
