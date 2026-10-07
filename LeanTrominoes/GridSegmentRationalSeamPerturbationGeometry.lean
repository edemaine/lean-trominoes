/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalSeamPerturbation

/-! # Shifted row-seam ports remain proper points of their original segments -/
namespace LeanTrominoes

namespace RationalPerturbation

theorem positiveMargin_le_one (values : List ℚ) : positiveMargin values ≤ 1 := by
  induction values with
  | nil => norm_num [positiveMargin]
  | cons head tail induction => exact (min_le_right _ _).trans induction

theorem slabPerturbation_lt_one (values : List (ℚ × ℚ)) : slabPerturbation values < 1 := by
  have first : margin values ≤ 1 := positiveMargin_le_one _
  have second := min_le_left (margin values) (positiveMargin (values.map fun value => OrthogonalDrawingRefinement.rationalSlabMargin value.1 value.2))
  unfold slabPerturbation
  linarith

end RationalPerturbation

namespace GridSegment

theorem rationalAbscissaAt_realInteriorContains {segment : GridSegment} {height : ℚ}
    (between : ((segment.start.2 : ℚ) < height ∧ height < segment.finish.2) ∨
      ((segment.finish.2 : ℚ) < height ∧ height < segment.start.2)) :
    segment.RealInteriorContains ((segment.rationalAbscissaAt height : ℝ),(height : ℝ)) := by
  have different : segment.finish.2 ≠ segment.start.2 := by
    intro equal
    rw [equal] at between
    rcases between with forward | backward <;> linarith
  have nonzero : (segment.finish.2 : ℝ)-segment.start.2 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast different)
  let parameter := ((height : ℝ)-segment.start.2)/((segment.finish.2 : ℝ)-segment.start.2)
  have bounds : 0 < parameter ∧ parameter < 1 := by
    rcases between with forward | backward
    · have lo : (segment.start.2 : ℝ) < (height : ℝ) := by exact_mod_cast forward.1
      have hi : (height : ℝ) < segment.finish.2 := by exact_mod_cast forward.2
      exact ⟨div_pos (by linarith) (by linarith),
        (div_lt_one (by linarith : (0 : ℝ) < segment.finish.2-segment.start.2)).mpr (by linarith)⟩
    · have lo : (segment.finish.2 : ℝ) < (height : ℝ) := by exact_mod_cast backward.1
      have hi : (height : ℝ) < segment.start.2 := by exact_mod_cast backward.2
      have opposite : parameter = ((segment.start.2 : ℝ)-height)/((segment.start.2 : ℝ)-segment.finish.2) := by
        dsimp only [parameter]
        have oppositeNonzero : (segment.start.2 : ℝ)-segment.finish.2 ≠ 0 := by linarith
        field_simp [nonzero,oppositeNonzero]
        ring
      rw [opposite]
      exact ⟨div_pos (by linarith) (by linarith),
        (div_lt_one (by linarith : (0 : ℝ) < segment.start.2-segment.finish.2)).mpr (by linarith)⟩
  refine ⟨parameter,bounds.1,bounds.2,?_,?_⟩
  · simp only [rationalAbscissaAt,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_intCast]
    dsimp only [parameter,Prod.fst]
    field_simp [nonzero] <;> ring
  · dsimp only [parameter,Prod.snd]
    rw [div_mul_cancel₀ _ nonzero]
    ring

theorem shifted_horizontal_seam_between {segment : GridSegment} {line : Int} {epsilon : ℚ}
    (crosses : segment.CrossesHorizontalLine line) (positive : 0 < epsilon) (small : epsilon < 1) :
    ((segment.start.2 : ℚ) < (line : ℚ)-epsilon ∧ (line : ℚ)-epsilon < segment.finish.2) ∨
      ((segment.finish.2 : ℚ) < (line : ℚ)-epsilon ∧ (line : ℚ)-epsilon < segment.start.2) := by
  change (segment.start.2 < line ∧ line < segment.finish.2) ∨
    (segment.finish.2 < line ∧ line < segment.start.2) at crosses
  rcases crosses with forward | backward
  · have lower : (segment.start.2 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.start.2+1 ≤ line)
    have upper : (line : ℚ) < segment.finish.2 := by exact_mod_cast forward.2
    exact Or.inl ⟨by linarith,by linarith⟩
  · have lower : (segment.finish.2 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.finish.2+1 ≤ line)
    have upper : (line : ℚ) < segment.start.2 := by exact_mod_cast backward.2
    exact Or.inr ⟨by linarith,by linarith⟩

theorem shifted_horizontal_seam_realInteriorContains {segment : GridSegment} {line : Int} {epsilon : ℚ}
    (crosses : segment.CrossesHorizontalLine line) (positive : 0 < epsilon) (small : epsilon < 1) :
    segment.RealInteriorContains ((segment.rationalAbscissaAt ((line : ℚ)-epsilon) : ℝ),((line : ℚ)-epsilon : ℝ)) := by
  simpa only [Rat.cast_sub,Rat.cast_intCast] using
    rationalAbscissaAt_realInteriorContains (shifted_horizontal_seam_between crosses positive small)

end GridSegment
end LeanTrominoes
