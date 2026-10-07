/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalPeriodicCoordinates
import Mathlib.Tactic

/-! # Consistent slab assignment for crossings exactly on integer columns

An integral crossing can belong to either adjacent slab. The chosen bias
commutes with integer translations and preserves the order of distinct
crossings, even when their biases differ.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def rationalSlab (coordinate : ℚ) (towardLeft : Bool) : Int :=
  if towardLeft ∧ coordinate = (⌊coordinate⌋ : Int) then ⌊coordinate⌋-1 else ⌊coordinate⌋

theorem rationalSlab_bounds (coordinate : ℚ) (towardLeft : Bool) :
    (rationalSlab coordinate towardLeft : ℚ) ≤ coordinate ∧ coordinate ≤ (rationalSlab coordinate towardLeft : ℚ)+1 := by
  have lo := Int.floor_le coordinate
  have hi := Int.lt_floor_add_one coordinate
  unfold rationalSlab
  split_ifs with biased
  · rw [biased.2]
    simp only [Int.floor_intCast]
    push_cast
    constructor <;> linarith
  · exact ⟨lo,hi.le⟩

theorem rationalSlab_translate (coordinate : ℚ) (towardLeft : Bool) (shift : Int) :
    rationalSlab (coordinate+shift) towardLeft = rationalSlab coordinate towardLeft+shift := by
  unfold rationalSlab
  rw [Int.floor_add_intCast]
  have equal : coordinate+(shift : ℚ) = ((⌊coordinate⌋+shift : Int) : ℚ) ↔ coordinate = (⌊coordinate⌋ : ℚ) := by
    push_cast
    constructor <;> intro equality <;> linarith
  simp only [equal]
  split_ifs <;> omega

theorem rationalSlab_order {first second : ℚ} (ordered : first < second) (firstBias secondBias : Bool) :
    rationalSlab first firstBias ≤ rationalSlab second secondBias := by
  have firstLo := Int.floor_le first
  have secondLo := Int.floor_le second
  have firstHi := Int.lt_floor_add_one first
  have secondHi := Int.lt_floor_add_one second
  have floors := Int.floor_mono ordered.le
  unfold rationalSlab
  split_ifs with firstIntegral secondIntegral secondIntegral
  · omega
  · omega
  · have strictFloors : ⌊first⌋ < ⌊second⌋ := by
      rw [secondIntegral.2] at ordered
      have strictCast : (⌊first⌋ : ℚ) < (⌊second⌋ : ℚ) := lt_of_le_of_lt firstLo ordered
      exact_mod_cast strictCast
    omega
  · exact floors

theorem rationalSlab_in_fundamental {period : Int} {coordinate : ℚ}
    (bounds : 0 < coordinate ∧ coordinate < period) (towardLeft : Bool) :
    0 ≤ rationalSlab coordinate towardLeft ∧ rationalSlab coordinate towardLeft < period := by
  have lo := Int.floor_le coordinate
  have hi := Int.lt_floor_add_one coordinate
  have floorNonnegative : 0 ≤ ⌊coordinate⌋ := Int.floor_nonneg.mpr bounds.1.le
  have floorUpper : ⌊coordinate⌋ < period := by exact_mod_cast lt_of_le_of_lt lo bounds.2
  unfold rationalSlab
  split_ifs with integral
  · have floorPositive : 0 < ⌊coordinate⌋ := by
      rw [integral.2] at bounds
      exact_mod_cast bounds.1
    omega
  · exact ⟨floorNonnegative,floorUpper⟩

end LeanTrominoes.OrthogonalDrawingRefinement
