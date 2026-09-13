/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSlabSymmetry
import LeanTrominoes.KeyedPolycubeSlabRecovery

/-! # Normalize an arbitrary slab tiling and recover a planar tiling -/

namespace LeanTrominoes.KeyedPeriodicComplement

private theorem normalize_unflipped {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (a : VoxelPlacement Bool) (ha : a ∈ placements) (hk : a.kind = true)
    (hf : a.symmetry.flip = false) :
    ∃ ps, IsVoxelTiling (slabFamily n holes) (voxelSlab 2) ps ∧ slabReference ∈ ps := by
  have horizontal := mixed_slab_horizontal hn holes a (tiling.tilesInside a ha)
  have height : a.offset.2 = 0 := by
    simpa [hf] using mixed_background_height hn holes admissible a hk (tiling.tilesInside a ha)
  let centered := tiling.recenter_slab a.offset.1
  have centeredHorizontal := fun p hp => mixed_slab_horizontal hn holes p (centered.tilesInside p hp)
  refine ⟨{p | (p.orient a.symmetry.planar).shift (a.offset.1, 0) ∈ placements},
    centered.reorient_slab centeredHorizontal a.symmetry.planar, ?_⟩
  have he : (slabReference.orient a.symmetry.planar).shift (a.offset.1, 0) = a := by
    apply VoxelPlacement.ext
    · exact hk.symm
    · change ⟨a.symmetry.planar.compose .identity, false, 0⟩ = a.symmetry
      rw [SquareSymmetry.compose_identity]
      cases hs : a.symmetry with
      | mk s f axis =>
        have hf' : f = false := by simpa [hs] using hf
        have ha' : axis = 0 := by simpa [hs] using horizontal
        simp [hf', ha']
    · change (Cell.add a.offset.1 (a.symmetry.planar.act (0, 0)), 0) = a.offset
      apply Prod.ext
      · simp [Cell.add]
      · exact height.symm
  change (slabReference.orient a.symmetry.planar).shift (a.offset.1, 0) ∈ placements
  rwa [he]

/-- Every mixed slab tiling can be moved and reflected to contain the
canonical Q at the origin with its cap on top. -/
theorem slab_normalize {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (slabFamily n holes) (voxelSlab 2)) :
    ∃ ps, IsVoxelTiling (slabFamily n holes) (voxelSlab 2) ps ∧ slabReference ∈ ps := by
  obtain ⟨ps, tiling⟩ := tileable
  obtain ⟨a, ha, hk⟩ := voxel_right_tile_occurs Polycube.bumpyOne (slabTile n holes)
    (voxelSlab 2) ps tiling Polycube.bumpyOne_not_tileable_slab_two
  cases hf : a.symmetry.flip with
  | false => exact normalize_unflipped hn holes admissible ps tiling a ha hk hf
  | true =>
    have reflected := tiling.reflect_slab (fun p hp => mixed_slab_horizontal hn holes p (tiling.tilesInside p hp))
    apply normalize_unflipped hn holes admissible _ reflected a.reflectSlab
    · change a.reflectSlab.reflectSlab ∈ ps
      simpa using ha
    · exact hk
    · simp [VoxelPlacement.reflectSlab, hf]

/-- No seed, alignment, or vertical-orientation hypothesis remains. -/
theorem planar_tileable_of_slab {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (slabFamily n holes) (voxelSlab 2)) :
    Tileable (planarFamily n holes) Set.univ := by
  obtain ⟨ps, ht, seed⟩ := slab_normalize hn holes admissible tileable
  exact planar_tileable_of_slab_seed hn period holes admissible ps ht seed

end LeanTrominoes.KeyedPeriodicComplement
