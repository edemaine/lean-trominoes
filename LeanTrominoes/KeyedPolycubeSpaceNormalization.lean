/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGrid
import LeanTrominoes.PolycubeSpaceSymmetry
import LeanTrominoes.BumpyPolycubeObstruction

/-! # Every full-space tiling admits a complete horizontal background grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem space_normalize (n : Nat) (holes : Polyomino)
    (tileable : VoxelTileable (spaceFamily n holes) Set.univ) :
    ∃ ps, IsVoxelTiling (spaceFamily n holes) Set.univ ps ∧
      SpaceCanonical ps ∧ spaceReference ∈ ps := by
  obtain ⟨ps,tiling⟩ := tileable
  obtain ⟨p,hp,hk⟩ := voxel_right_tile_occurs Polycube.bumpyThree (spaceTile n holes)
    Set.univ ps tiling Polycube.bumpyThree_not_tileable_space
  obtain ⟨qs,ht,seed⟩ := tiling.normalize_space p hp
  have ref : spaceReference ∈ qs := by simpa [spaceReference,referencePlacement,Placement.toVoxel,CubeSymmetry.identity,hk] using seed
  refine ⟨canonicalSpacePlacement '' qs,space_tiling_canonical ht,?_,?_⟩
  · exact fun _ hp hk ha => space_canonical_unflipped hp hk ha
  · refine ⟨spaceReference,ref,?_⟩
    simp [canonicalSpacePlacement,spaceReference,referencePlacement,Placement.toVoxel]

theorem space_tileable_has_grid {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (spaceFamily n holes) Set.univ) :
    ∃ ps, IsVoxelTiling (spaceFamily n holes) Set.univ ps ∧
      ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ ps := by
  obtain ⟨ps,ht,hc,seed⟩ := space_normalize n holes tileable
  exact space_exists_tiling_with_grid hn period holes admissible ps ht hc seed

end LeanTrominoes.KeyedPeriodicComplement
