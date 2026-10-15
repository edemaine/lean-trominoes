/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalSeamPerturbationGeometry
import LeanTrominoes.Common.Geometry.GridSegmentRealIntersection

/-! # A contact with a shifted row seam comes from an integer row-seam crossing -/
namespace LeanTrominoes.GridSegment

theorem shifted_seam_contact_crosses {segment : GridSegment} {line : Int} {epsilon : ℚ} {abscissa : ℝ}
    (positive : 0 < epsilon) (small : epsilon < 1)
    (startAway : segment.start.2 ≠ line) (finishAway : segment.finish.2 ≠ line)
    (contains : segment.RealContains (abscissa,((line : ℚ)-epsilon : ℝ))) :
    segment.CrossesHorizontalLine line := by
  have box := realBoxContains_of_realContains contains
  have lower : min segment.start.2 segment.finish.2 < line := by
    have below : ((min segment.start.2 segment.finish.2 : Int) : ℝ) < (line : ℝ) := by
      have positiveReal : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast positive
      have bound := box.2.2.1
      dsimp only [Prod.snd] at bound
      push_cast at bound ⊢
      linarith
    exact_mod_cast below
  have upper : line ≤ max segment.start.2 segment.finish.2 := by
    have above : (line : ℝ)-1 < ((max segment.start.2 segment.finish.2 : Int) : ℝ) := by
      have smallReal : (epsilon : ℝ) < 1 := by exact_mod_cast small
      have bound := box.2.2.2
      dsimp only [Prod.snd] at bound
      push_cast at bound ⊢
      linarith
    have integerBound : line-1 < max segment.start.2 segment.finish.2 := by exact_mod_cast above
    omega
  change (segment.start.2 < line ∧ line < segment.finish.2) ∨ (segment.finish.2 < line ∧ line < segment.start.2)
  omega

end LeanTrominoes.GridSegment
