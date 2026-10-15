/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineRectangleClips
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalRectangleBoundaryPoints

/-! # An affine line entering the real rectangle has rational boundary contacts -/
namespace LeanTrominoes.RationalAffineBoundary

theorem endpoint_cases_of_real_interior {width height base slope : ℚ} {x y : ℝ}
    (firstNotBottom : base ≠ 0) (firstNotTop : base ≠ height)
    (lastNotBottom : base+slope*width ≠ 0) (lastNotTop : base+slope*width ≠ height)
    (coordinateBounds : 0 ≤ x ∧ x ≤ (width : ℝ)) (heightBounds : 0 < y ∧ y < (height : ℝ))
    (lineEquation : y = (base : ℝ)+(slope : ℝ)*x) :
    (0 < base ∧ base < height) ∨ (0 < base+slope*width ∧ base+slope*width < height) ∨
      (base < 0 ∧ height < base+slope*width) ∨ (base+slope*width < 0 ∧ height < base) := by
  by_cases nonnegative : (0 : ℝ) ≤ slope
  · have lo := mul_nonneg nonnegative coordinateBounds.1
    have hi := mul_le_mul_of_nonneg_left coordinateBounds.2 nonnegative
    have endPositiveReal : (0 : ℝ) < (base : ℝ)+(slope : ℝ)*(width : ℝ) := by linarith [heightBounds.1]
    have baseBelowReal : (base : ℝ) < (height : ℝ) := by linarith [heightBounds.2]
    have endPositive : 0 < base+slope*width := by exact_mod_cast endPositiveReal
    have baseBelow : base < height := by exact_mod_cast baseBelowReal
    by_cases firstPositive : 0 < base
    · exact Or.inl ⟨firstPositive,baseBelow⟩
    · by_cases lastBelow : base+slope*width < height
      · exact Or.inr (Or.inl ⟨endPositive,lastBelow⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨lt_of_le_of_ne (le_of_not_gt firstPositive) firstNotBottom,
          lt_of_le_of_ne (le_of_not_gt lastBelow) lastNotTop.symm⟩))
  · have lo := mul_le_mul_of_nonpos_left coordinateBounds.2 (le_of_not_ge nonnegative)
    have hi := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge nonnegative) coordinateBounds.1
    have basePositiveReal : (0 : ℝ) < (base : ℝ) := by linarith [heightBounds.1]
    have endBelowReal : (base : ℝ)+(slope : ℝ)*(width : ℝ) < (height : ℝ) := by linarith [heightBounds.2]
    have basePositive : 0 < base := by exact_mod_cast basePositiveReal
    have endBelow : base+slope*width < height := by exact_mod_cast endBelowReal
    by_cases lastPositive : 0 < base+slope*width
    · exact Or.inr (Or.inl ⟨lastPositive,endBelow⟩)
    · by_cases firstBelow : base < height
      · exact Or.inl ⟨basePositive,firstBelow⟩
      · exact Or.inr (Or.inr (Or.inr ⟨lt_of_le_of_ne (le_of_not_gt lastPositive) lastNotBottom,
          lt_of_le_of_ne (le_of_not_gt firstBelow) firstNotTop.symm⟩))

theorem contact_exists_of_real_interior {width height base slope : ℚ} {x y : ℝ}
    (widthPositive : 0 < width) (heightPositive : 0 < height)
    (firstNotBottom : base ≠ 0) (firstNotTop : base ≠ height)
    (lastNotBottom : base+slope*width ≠ 0) (lastNotTop : base+slope*width ≠ height)
    (coordinateBounds : 0 ≤ x ∧ x ≤ (width : ℝ)) (heightBounds : 0 < y ∧ y < (height : ℝ))
    (lineEquation : y = (base : ℝ)+(slope : ℝ)*x) :
    ∃ point : ℚ × ℚ, Contact width height base slope point := by
  rcases endpoint_cases_of_real_interior firstNotBottom firstNotTop lastNotBottom lastNotTop coordinateBounds heightBounds lineEquation with
    firstInside | lastInside | increasing | decreasing
  · exact ⟨(0,base),⟨by simp,Or.inl ⟨Or.inl rfl,firstInside⟩⟩⟩
  · exact ⟨(width,base+slope*width),⟨rfl,Or.inl ⟨Or.inr rfl,lastInside⟩⟩⟩
  · obtain ⟨bottom,lo,hi,equal⟩ := affine_intermediate (base := base) (slope := slope) (value := 0)
      widthPositive (Or.inl ⟨by simpa using increasing.1,by linarith [increasing.2]⟩)
    exact ⟨(bottom,0),⟨equal.symm,Or.inr ⟨Or.inl rfl,lo,hi⟩⟩⟩
  · obtain ⟨bottom,lo,hi,equal⟩ := affine_intermediate (base := base) (slope := slope) (value := 0)
      widthPositive (Or.inr ⟨decreasing.1,by simpa using (heightPositive.trans decreasing.2)⟩)
    exact ⟨(bottom,0),⟨equal.symm,Or.inr ⟨Or.inl rfl,lo,hi⟩⟩⟩

end LeanTrominoes.RationalAffineBoundary
