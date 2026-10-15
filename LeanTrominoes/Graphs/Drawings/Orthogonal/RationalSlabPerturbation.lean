/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalSlabAssignment
import LeanTrominoes.Graphs.Drawings.Grid.FiniteRationalPerturbation

/-! # Small rational perturbations realize the biased integer-slab assignment -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def rationalSlabMargin (coordinate velocity : ℚ) : ℚ :=
  (if coordinate = (⌊coordinate⌋ : ℚ) then 1 else
    min (coordinate-(⌊coordinate⌋ : ℚ)) ((⌊coordinate⌋ : ℚ)+1-coordinate))/(1+|velocity|)

theorem rationalSlabMargin_positive (coordinate velocity : ℚ) : 0 < rationalSlabMargin coordinate velocity := by
  have lower := Int.floor_le coordinate
  have upper := Int.lt_floor_add_one coordinate
  unfold rationalSlabMargin
  split_ifs with integral
  · exact div_pos (by norm_num) (by positivity)
  · apply div_pos _ (by positivity)
    apply lt_min
    · have strict : (⌊coordinate⌋ : ℚ) < coordinate := lt_of_le_of_ne lower (Ne.symm integral)
      linarith
    · linarith

theorem rationalSlab_perturbation {coordinate velocity epsilon : ℚ} (positive : 0 < epsilon)
    (small : epsilon < rationalSlabMargin coordinate velocity) :
    rationalSlab (coordinate+epsilon*velocity) false = rationalSlab coordinate (decide (velocity < 0)) := by
  have lower := Int.floor_le coordinate
  have upper := Int.lt_floor_add_one coordinate
  have velocityLo := neg_abs_le velocity
  have velocityHi := le_abs_self velocity
  have perturbLo := mul_le_mul_of_nonneg_left velocityLo positive.le
  have perturbHi := mul_le_mul_of_nonneg_left velocityHi positive.le
  by_cases integral : coordinate = (⌊coordinate⌋ : ℚ)
  · have scaled : epsilon*(1+|velocity|) < 1 := by
      unfold rationalSlabMargin at small
      rw [if_pos integral] at small
      exact (lt_div_iff₀ (by positivity : (0 : ℚ) < 1+|velocity|)).mp small
    by_cases negative : velocity < 0
    · have productNegative : epsilon*velocity < 0 := mul_neg_of_pos_of_neg positive negative
      have floorEq : ⌊coordinate+epsilon*velocity⌋ = ⌊coordinate⌋-1 := by
        apply Int.floor_eq_iff.mpr
        push_cast
        constructor <;> nlinarith
      simp only [rationalSlab,Bool.false_eq_true,false_and,ite_false,floorEq,decide_eq_true_eq,
        negative,true_and,if_pos integral]
    · have productNonnegative : 0 ≤ epsilon*velocity := mul_nonneg positive.le (le_of_not_gt negative)
      have floorEq : ⌊coordinate+epsilon*velocity⌋ = ⌊coordinate⌋ := by
        apply Int.floor_eq_iff.mpr
        constructor <;> nlinarith
      simp only [rationalSlab,Bool.false_eq_true,false_and,ite_false,floorEq,decide_eq_true_eq,
        negative,false_and]
  · have scaled : epsilon*(1+|velocity|) <
        min (coordinate-(⌊coordinate⌋ : ℚ)) ((⌊coordinate⌋ : ℚ)+1-coordinate) := by
      unfold rationalSlabMargin at small
      rw [if_neg integral] at small
      exact (lt_div_iff₀ (by positivity : (0 : ℚ) < 1+|velocity|)).mp small
    have belowLower := lt_of_lt_of_le scaled (min_le_left _ _)
    have belowUpper := lt_of_lt_of_le scaled (min_le_right _ _)
    have floorEq : ⌊coordinate+epsilon*velocity⌋ = ⌊coordinate⌋ := by
      apply Int.floor_eq_iff.mpr
      constructor <;> nlinarith
    simp only [rationalSlab,Bool.false_eq_true,false_and,ite_false,floorEq,integral,and_false]

end LeanTrominoes.OrthogonalDrawingRefinement
