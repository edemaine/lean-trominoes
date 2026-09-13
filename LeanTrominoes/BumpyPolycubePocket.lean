/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubePocketFirst
import LeanTrominoes.BumpyPolycubePocketSecond

/-! # The two pocket voxels of the thickness-three extrusion

The finite certificates check orientation/source-voxel pairs directly,
including all orientations of both the reference tile and its neighbors.
-/

namespace LeanTrominoes.Polycube.BumpyPocket

theorem first_pocket (s : CubeSymmetry) (p : VoxelPlacement Unit)
    (hp : p ∈ candidates s ((1, 1), 1)) :
    s.act ((1, 2), 1) ∈ p.cells family ∧ s.act ((2, 1), 1) ∉ p.cells family := by
  obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
  simpa only [covers_iff] using first_source_certificate s t c hc
    (compatible_of_disjoint s _ hd)

theorem second_pocket (s : CubeSymmetry) (p : VoxelPlacement Unit)
    (hp : p ∈ candidates s ((2, 1), 1)) :
    s.act ((1, 2), 1) ∈ p.cells family := by
  obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
  exact (covers_iff _ _).mp (second_source_certificate s t c hc
    (compatible_of_disjoint s _ hd))

theorem pockets_outside :
    ∀ s : CubeSymmetry,
      s.act ((1, 1), 1) ∉ (VoxelPlacement.reference s).cells family ∧
      s.act ((2, 1), 1) ∉ (VoxelPlacement.reference s).cells family := by decide +kernel

end LeanTrominoes.Polycube.BumpyPocket
