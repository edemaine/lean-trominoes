/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundarySlabSeparation

/-! # A column strip can touch an adjacent routing slab only on its boundary -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

theorem strip_slab_contact_vertical_boundary {pitch radius column line : Int}
    (spacing : 10*radius < pitch) (nonnegative : 0 ≤ radius) {point : ℝ}
    (strip : |point-(pitch : ℝ)*line| ≤ 5*(radius : ℝ))
    (slab : (pitch : ℝ)*column+5*(radius : ℝ) ≤ point ∧
      point ≤ (pitch : ℝ)*(column+1)-5*(radius : ℝ)) :
    (line = column ∧ point = (pitch : ℝ)*column+5*(radius : ℝ)) ∨
      (line = column+1 ∧ point = (pitch : ℝ)*(column+1)-5*(radius : ℝ)) := by
  have gap : 10*(radius : ℝ) < pitch := by exact_mod_cast spacing
  have radiusPositive : (0 : ℝ) ≤ radius := by exact_mod_cast nonnegative
  have pitchPositive : (0 : ℝ) < pitch := by linarith
  have bounds := abs_le.mp strip
  by_cases atLeft : line = column
  · subst line
    exact Or.inl ⟨rfl,by linarith [slab.1,bounds.2]⟩
  by_cases atRight : line = column+1
  · subst line
    push_cast at bounds
    exact Or.inr ⟨rfl,by linarith [slab.2,bounds.1]⟩
  rcases lt_or_gt_of_ne atLeft with before | after
  · have step : (line : ℝ)+1 ≤ column := by exact_mod_cast (by omega : line+1 ≤ column)
    have scaled := mul_le_mul_of_nonneg_left step pitchPositive.le
    exfalso
    nlinarith [slab.1,bounds.2]
  · have step : (column : ℝ)+2 ≤ line := by exact_mod_cast (by omega : column+2 ≤ line)
    have scaled := mul_le_mul_of_nonneg_left step pitchPositive.le
    exfalso
    nlinarith [slab.2,bounds.1]

end LeanTrominoes.OrthogonalBoundaryRouting
