/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-! # Exact boundary contacts of an affine line with a rational rectangle -/
namespace LeanTrominoes.RationalAffineBoundary

def Contact (width height base slope : ℚ) (point : ℚ × ℚ) : Prop :=
  point.2 = base+slope*point.1 ∧
    (((point.1 = 0 ∨ point.1 = width) ∧ 0 < point.2 ∧ point.2 < height) ∨
      ((point.2 = 0 ∨ point.2 = height) ∧ 0 < point.1 ∧ point.1 < width))

theorem affine_intermediate {base slope left right value : ℚ} (increasingX : left < right)
    (between : (base+slope*left < value ∧ value < base+slope*right) ∨
      (base+slope*right < value ∧ value < base+slope*left)) :
    ∃ coordinate, left < coordinate ∧ coordinate < right ∧ base+slope*coordinate = value := by
  let first := base+slope*left
  let last := base+slope*right
  let parameter := (value-first)/(last-first)
  have nonzero : last-first ≠ 0 := by rcases between with forward | backward <;> dsimp [first,last] <;> linarith
  have bounds : 0 < parameter ∧ parameter < 1 := by
    rcases between with forward | backward
    · have denominatorPositive : 0 < last-first := by dsimp [first,last]; linarith
      exact ⟨div_pos (by dsimp [first]; linarith) denominatorPositive,
        (div_lt_one denominatorPositive).mpr (by dsimp [first,last]; linarith)⟩
    · have denominatorPositive : 0 < first-last := by dsimp [first,last]; linarith
      have opposite : parameter = (first-value)/(first-last) := by
        dsimp [parameter]
        field_simp [nonzero,neg_ne_zero.mpr nonzero]
        <;> ring
      rw [opposite]
      exact ⟨div_pos (by dsimp [first]; linarith) denominatorPositive,
        (div_lt_one denominatorPositive).mpr (by dsimp [first,last]; linarith)⟩
  refine ⟨left+parameter*(right-left),?_,?_,?_⟩
  · have positiveProduct := mul_pos bounds.1 (sub_pos.mpr increasingX)
    linarith
  · have positiveProduct := mul_pos (sub_pos.mpr bounds.2) (sub_pos.mpr increasingX)
    nlinarith
  · dsimp [parameter,first,last]
    have denominatorNonzero : (base+slope*right)-(base+slope*left) ≠ 0 := nonzero
    field_simp [denominatorNonzero]
    <;> ring

theorem affine_value_between_endpoints {width base slope coordinate : ℚ}
    (coordinateBounds : 0 ≤ coordinate ∧ coordinate ≤ width) :
    min base (base+slope*width) ≤ base+slope*coordinate ∧
      base+slope*coordinate ≤ max base (base+slope*width) := by
  by_cases nonnegative : 0 ≤ slope
  · have lower := mul_nonneg nonnegative coordinateBounds.1
    have upper := mul_le_mul_of_nonneg_left coordinateBounds.2 nonnegative
    constructor
    · exact (min_le_left _ _).trans (by linarith)
    · exact (show base+slope*coordinate ≤ base+slope*width by linarith).trans (le_max_right _ _)
  · have lower := mul_le_mul_of_nonpos_left coordinateBounds.2 (le_of_not_ge nonnegative)
    have upper := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge nonnegative) coordinateBounds.1
    constructor
    · exact (min_le_right _ _).trans (by linarith)
    · exact (show base+slope*coordinate ≤ base by linarith).trans (le_max_left _ _)

end LeanTrominoes.RationalAffineBoundary
