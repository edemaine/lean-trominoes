/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubePocket

/-! # The fixed 45-cube tile cannot tile three-dimensional space -/

namespace LeanTrominoes.Polycube

open VoxelPlacement BumpyPocket

/-- The thickness-three extrusion cannot tile space, even with reflections. -/
theorem bumpyThree_not_tileable_space : ¬ VoxelTileableBy bumpyThree Set.univ := by
  rintro ⟨placements, tiling⟩
  obtain ⟨base, hbase, -⟩ := tiling.exists_cover (Set.mem_univ ((0, 0), 0))
  let s := base.symmetry
  obtain ⟨a, ha, hca⟩ := tiling.exists_cover
    (Set.mem_univ (Voxel.add base.offset (s.act ((1, 1), 1))))
  obtain ⟨b, hb, hcb⟩ := tiling.exists_cover
    (Set.mem_univ (Voxel.add base.offset (s.act ((2, 1), 1))))
  have ra : s.act ((1, 1), 1) ∈ (relative base.offset a).cells family :=
    (mem_relative _ _ _ _).mpr hca
  have rb : s.act ((2, 1), 1) ∈ (relative base.offset b).cells family :=
    (mem_relative _ _ _ _).mpr hcb
  have nea : base ≠ a := by
    rintro rfl
    rw [relative_self] at ra
    exact (pockets_outside s).1 ra
  have neb : base ≠ b := by
    rintro rfl
    rw [relative_self] at rb
    exact (pockets_outside s).2 rb
  have da := disjoint_relative family base.offset base a (tiling.disjoint_cells hbase ha nea)
  have db := disjoint_relative family base.offset base b (tiling.disjoint_cells hbase hb neb)
  rw [relative_self] at da db
  have ac : relative base.offset a ∈ candidates s ((1, 1), 1) :=
    Finset.mem_filter.mpr ⟨(mem_coveringPlacements _ _ _).mpr ra, da⟩
  have bc : relative base.offset b ∈ candidates s ((2, 1), 1) :=
    Finset.mem_filter.mpr ⟨(mem_coveringPlacements _ _ _).mpr rb, db⟩
  obtain ⟨sharedA, excludesB⟩ := first_pocket s _ ac
  have sharedB := second_pocket s _ bc
  have neab : a ≠ b := by
    rintro rfl
    exact excludesB rb
  have disjointAB := disjoint_relative family base.offset a b (tiling.disjoint_cells ha hb neab)
  exact (Finset.disjoint_left.mp disjointAB) sharedA sharedB

end LeanTrominoes.Polycube
