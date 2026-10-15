/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalPerturbation

/-! # Exact parameters order route pieces independently of edge direction and period -/
namespace LeanTrominoes.GridSegment

def rationalXParameter (segment : GridSegment) (coordinate : ℚ) : ℚ :=
  (coordinate-(segment.start.1 : ℚ))/((segment.finish.1 : ℚ)-segment.start.1)

theorem rationalXParameter_in_unit_interval {segment : GridSegment} {coordinate : ℚ}
    (between : ((segment.start.1 : ℚ) < coordinate ∧ coordinate < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < coordinate ∧ coordinate < segment.start.1)) :
    0 < segment.rationalXParameter coordinate ∧ segment.rationalXParameter coordinate < 1 := by
  unfold rationalXParameter
  rcases between with forward | backward
  · have denominatorPositive : (0 : ℚ) < (segment.finish.1 : ℚ)-segment.start.1 := by linarith
    exact ⟨div_pos (by linarith) denominatorPositive,(div_lt_iff₀ denominatorPositive).mpr (by linarith)⟩
  · have denominatorNegative : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg (by linarith) denominatorNegative,(div_lt_iff_of_neg denominatorNegative).mpr (by linarith)⟩

theorem rationalXParameter_injective {segment : GridSegment} (nonvertical : segment.start.1 ≠ segment.finish.1) :
    Function.Injective segment.rationalXParameter := by
  intro first last equal
  have denominatorNonzero : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) ≠ 0 := by
    intro zero
    apply nonvertical
    exact_mod_cast (by linarith : (segment.start.1 : ℚ) = segment.finish.1)
  have numeratorEqual := (div_left_inj' denominatorNonzero).mp equal
  linarith

theorem rationalXParameter_translate (segment : GridSegment) (offset : Cell) (coordinate : ℚ) :
    (segment.translate offset).rationalXParameter (coordinate+(offset.1 : ℚ)) = segment.rationalXParameter coordinate := by
  simp [rationalXParameter,translate,Cell.add]
  ring

end LeanTrominoes.GridSegment
