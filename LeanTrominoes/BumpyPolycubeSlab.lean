/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeHorizontalSlice
import LeanTrominoes.BumpyTrominoObstruction

/-! # The fixed 15-cube tile cannot tile the height-two slab alone -/

namespace LeanTrominoes.Polycube

private theorem upright_span :
    ∀ s : CubeSymmetry, s.axis ≠ 0 →
      ∃ a ∈ bumpyOne, ∃ b ∈ bumpyOne, (s.act a).2 + 2 ≤ (s.act b).2 := by
  decide +kernel

/-- Every copy of P that fits in two layers is horizontal. -/
theorem bumpyOne_horizontal (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => bumpyOne), c ∈ voxelSlab 2) :
    p.symmetry.axis = 0 := by
  by_contra hn
  obtain ⟨a, ha, b, hb, span⟩ := upright_span p.symmetry hn
  have ha' := inside (Voxel.add p.offset (p.symmetry.act a))
    ((p.mem_cells_iff _ _).mpr ⟨a, ha, rfl⟩)
  have hb' := inside (Voxel.add p.offset (p.symmetry.act b))
    ((p.mem_cells_iff _ _).mpr ⟨b, hb, rfl⟩)
  simp only [voxelSlab, Set.mem_setOf_eq, Voxel.add] at ha' hb'
  omega

theorem bumpyOne_not_tileable_slab_two : ¬ VoxelTileableBy bumpyOne (voxelSlab 2) := by
  rintro ⟨placements, tiling⟩
  apply PlusRefinement.bumpy_not_tileable_plane
  exact planar_tileable_of_horizontal_slab (fun _ : Unit => PlusRefinement.bumpy)
    (by decide : 0 < 2) tiling
    (fun p hp => bumpyOne_horizontal p (tiling.tilesInside p hp))

end LeanTrominoes.Polycube
