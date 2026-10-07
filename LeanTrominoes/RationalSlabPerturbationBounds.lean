/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalSlabPerturbation

/-! # Nonvertical shifted seam crossings avoid every integer column -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem rationalSlab_perturbation_strict_bounds {coordinate velocity epsilon : ℚ} (positive : 0 < epsilon)
    (small : epsilon < rationalSlabMargin coordinate velocity) (nonzero : velocity ≠ 0) :
    (rationalSlab coordinate (decide (velocity < 0)) : ℚ) < coordinate+epsilon*velocity ∧
      coordinate+epsilon*velocity < (rationalSlab coordinate (decide (velocity < 0)) : ℚ)+1 := by
  have falseSlab : rationalSlab (coordinate+epsilon*velocity) false = ⌊coordinate+epsilon*velocity⌋ := by
    simp [rationalSlab]
  have floorEq := falseSlab.symm.trans (rationalSlab_perturbation positive small)
  have velocityLo := neg_abs_le velocity
  have perturbLo := mul_le_mul_of_nonneg_left velocityLo positive.le
  constructor
  · by_cases integral : coordinate = (⌊coordinate⌋ : ℚ)
    · have scaled : epsilon*(1+|velocity|) < 1 := by
        unfold rationalSlabMargin at small
        rw [if_pos integral] at small
        exact (lt_div_iff₀ (by positivity : (0 : ℚ) < 1+|velocity|)).mp small
      by_cases negative : velocity < 0
      · have baseSlab : rationalSlab coordinate (decide (velocity < 0)) = ⌊coordinate⌋-1 := by
          simp only [rationalSlab,decide_eq_true_eq,negative,true_and,if_pos integral]
        rw [baseSlab]
        push_cast
        nlinarith
      · have velocityPositive : 0 < velocity := lt_of_le_of_ne (le_of_not_gt negative) (Ne.symm nonzero)
        have productPositive := mul_pos positive velocityPositive
        have baseSlab : rationalSlab coordinate (decide (velocity < 0)) = ⌊coordinate⌋ := by
          simp only [rationalSlab,decide_eq_true_eq,negative,false_and,ite_false]
        rw [baseSlab]
        linarith
    · have scaled : epsilon*(1+|velocity|) <
          min (coordinate-(⌊coordinate⌋ : ℚ)) ((⌊coordinate⌋ : ℚ)+1-coordinate) := by
        unfold rationalSlabMargin at small
        rw [if_neg integral] at small
        exact (lt_div_iff₀ (by positivity : (0 : ℚ) < 1+|velocity|)).mp small
      have belowLower := lt_of_lt_of_le scaled (min_le_left _ _)
      have baseSlab : rationalSlab coordinate (decide (velocity < 0)) = ⌊coordinate⌋ := by
        simp only [rationalSlab,integral,and_false,ite_false]
      rw [baseSlab]
      nlinarith
  · simpa only [floorEq] using Int.lt_floor_add_one (coordinate+epsilon*velocity)

end LeanTrominoes.OrthogonalDrawingRefinement
