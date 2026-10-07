/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Computable cell quotients and remainders of rational coordinates -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def rationalCell (period : Int) (coordinate : ℚ) : Int := ⌊coordinate/(period : ℚ)⌋
def rationalResidue (period : Int) (coordinate : ℚ) : ℚ := coordinate-(period : ℚ)*rationalCell period coordinate

theorem rationalResidue_bounds {period : Int} (positive : 0 < period) (coordinate : ℚ) :
    0 ≤ rationalResidue period coordinate ∧ rationalResidue period coordinate < period := by
  have periodPositive : (0 : ℚ) < period := by exact_mod_cast positive
  have lower := Int.floor_le (coordinate/(period : ℚ))
  have upper := Int.lt_floor_add_one (coordinate/(period : ℚ))
  have lowerScaled := mul_le_mul_of_nonneg_left lower periodPositive.le
  have upperScaled := mul_lt_mul_of_pos_left upper periodPositive
  rw [mul_div_cancel₀ _ periodPositive.ne'] at lowerScaled upperScaled
  unfold rationalResidue rationalCell
  constructor <;> linarith

theorem rationalCell_translate {period : Int} (positive : 0 < period) (coordinate : ℚ) (shift : Int) :
    rationalCell period (coordinate+(period : ℚ)*shift) = rationalCell period coordinate+shift := by
  have nonzero : (period : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have quotient : (coordinate+(period : ℚ)*shift)/(period : ℚ) = coordinate/(period : ℚ)+(shift : ℚ) := by
    field_simp [nonzero]
  unfold rationalCell
  rw [quotient,Int.floor_add_intCast]

theorem rationalResidue_translate {period : Int} (positive : 0 < period) (coordinate : ℚ) (shift : Int) :
    rationalResidue period (coordinate+(period : ℚ)*shift) = rationalResidue period coordinate := by
  unfold rationalResidue
  rw [rationalCell_translate positive]
  push_cast
  ring

theorem rationalCell_of_in_cell {period : Int} (positive : 0 < period) {coordinate : ℚ}
    (bounds : 0 ≤ coordinate ∧ coordinate < period) : rationalCell period coordinate = 0 := by
  have periodPositive : (0 : ℚ) < period := by exact_mod_cast positive
  apply Int.floor_eq_iff.mpr
  constructor
  · simpa using div_nonneg bounds.1 periodPositive.le
  · simpa using (div_lt_one periodPositive).mpr bounds.2

theorem rationalResidue_of_in_cell {period : Int} (positive : 0 < period) {coordinate : ℚ}
    (bounds : 0 ≤ coordinate ∧ coordinate < period) : rationalResidue period coordinate = coordinate := by
  simp [rationalResidue,rationalCell_of_in_cell positive bounds]

theorem rationalCoordinate_decomposition (period : Int) (coordinate : ℚ) :
    coordinate = (period : ℚ)*rationalCell period coordinate+rationalResidue period coordinate := by
  unfold rationalResidue
  ring

theorem rationalCell_monotone {period : Int} (positive : 0 < period) : Monotone (rationalCell period) := by
  intro first second ordered
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right ordered (by exact_mod_cast positive.le)

end LeanTrominoes.OrthogonalDrawingRefinement
