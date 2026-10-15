/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalSlabPerturbation

/-! # One computable perturbation preserves all crossing orders and slab choices -/
namespace LeanTrominoes.RationalPerturbation
open OrthogonalDrawingRefinement

def slabPerturbation (values : List (ℚ × ℚ)) : ℚ :=
  min (margin values) (positiveMargin (values.map fun value => rationalSlabMargin value.1 value.2))/2

theorem slabPerturbation_positive (values : List (ℚ × ℚ)) : 0 < slabPerturbation values := by
  unfold slabPerturbation
  apply div_pos _ (by norm_num)
  apply lt_min (margin_positive values)
  apply positiveMargin_positive
  intro bound member
  obtain ⟨coordinate,_,rfl⟩ := List.mem_map.mp member
  exact rationalSlabMargin_positive _ _

theorem slabPerturbation_le_margin (values : List (ℚ × ℚ)) : slabPerturbation values ≤ margin values := by
  have positive := slabPerturbation_positive values
  have bound := min_le_left (margin values) (positiveMargin (values.map fun value => rationalSlabMargin value.1 value.2))
  unfold slabPerturbation at positive ⊢
  linarith

theorem slabPerturbation_lt_slabMargin {values : List (ℚ × ℚ)} {coordinate : ℚ × ℚ}
    (member : coordinate ∈ values) : slabPerturbation values < rationalSlabMargin coordinate.1 coordinate.2 := by
  have positive := slabPerturbation_positive values
  have bound := min_le_right (margin values) (positiveMargin (values.map fun value => rationalSlabMargin value.1 value.2))
  have individual : positiveMargin (values.map fun value => rationalSlabMargin value.1 value.2) ≤
      rationalSlabMargin coordinate.1 coordinate.2 := positiveMargin_le (List.mem_map.mpr ⟨coordinate,member,rfl⟩)
  unfold slabPerturbation at positive ⊢
  linarith

theorem slabPerturbation_preserves_order {values : List (ℚ × ℚ)} {first second : ℚ × ℚ}
    (firstMember : first ∈ values) (secondMember : second ∈ values) (ordered : Before first second) :
    evaluate (slabPerturbation values) first < evaluate (slabPerturbation values) second :=
  evaluate_order (slabPerturbation_positive values) (slabPerturbation_le_margin values) firstMember secondMember ordered

theorem slabPerturbation_realizes_bias {values : List (ℚ × ℚ)} {coordinate : ℚ × ℚ}
    (member : coordinate ∈ values) :
    rationalSlab (evaluate (slabPerturbation values) coordinate) false =
      rationalSlab coordinate.1 (decide (coordinate.2 < 0)) :=
  rationalSlab_perturbation (slabPerturbation_positive values) (slabPerturbation_lt_slabMargin member)

end LeanTrominoes.RationalPerturbation
