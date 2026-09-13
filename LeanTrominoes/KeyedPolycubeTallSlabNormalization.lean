/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabGrid
import LeanTrominoes.PolycubeRegionNormalization

/-! # An arbitrary taller-slab tiling admits the canonical background grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_slab_normalize {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (tallSlabFamily height n holes) (voxelSlab height)) :
    ∃ ps, IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) ps ∧ tallSlabReference ∈ ps := by
  obtain ⟨ps,tiling⟩ := tileable
  obtain ⟨p,hp,hk⟩ := voxel_right_tile_occurs (TwoConnectedPolycubes.slabSmall height)
    (tallSlabTile height n holes) (voxelSlab height) ps tiling
    (TwoConnectedPolycubes.slabSmall_not_tileable (by omega))
  have eq : p.cells (tallSlabFamily height n holes) = p.untag.cells (fun _ => tallSlabTile height n holes) := by
    simp [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,hk]
  have inside := tiling.tilesInside p hp
  rw [eq] at inside
  have horizontal : p.symmetry.axis = 0 := tallSlabTile_horizontal hh wide holes p.untag inside
  have heightEq : p.offset.2 = if p.symmetry.flip then (height : Int)-1 else 0 :=
    tallSlabTile_vertical_offset hh wide hn holes admissible p.untag inside
  have invariant : ∀ c, Voxel.add p.offset (p.symmetry.act c) ∈ voxelSlab height ↔ c ∈ voxelSlab height := by
    intro c
    cases hf : p.symmetry.flip <;>
      simp [voxelSlab,Voxel.add,CubeSymmetry.act,horizontal,CubeSymmetry.cycle,hf] at * <;> omega
  obtain ⟨qs,ht,seed⟩ := tiling.normalize_preserving p hp invariant
  refine ⟨qs,ht,?_⟩
  simpa [tallSlabReference,referencePlacement,Placement.toVoxel,CubeSymmetry.identity,hk] using seed

theorem tall_slab_tileable_has_grid {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (tallSlabFamily height n holes) (voxelSlab height)) :
    ∃ ps, IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) ps ∧
      ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ ps := by
  obtain ⟨ps,ht,seed⟩ := tall_slab_normalize hh wide hn holes admissible tileable
  exact tall_slab_exists_tiling_with_grid hh wide hn period holes admissible ps ht seed

end LeanTrominoes.KeyedPeriodicComplement
