/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceMiddle
import LeanTrominoes.KeyedPolycubeSpaceNormalization
import LeanTrominoes.BumpyPolycubeThreeSlices

/-! # Recovering a planar tiling from an arbitrary full-space tiling -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem space_middle_slice {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements)
    (meets : ∃ a : Cell, (a,1) ∈ p.cells (spaceFamily n holes)) (c : Cell) :
    (c,1) ∈ p.cells (spaceFamily n holes) ↔
      c ∈ p.toPlanar.cells (pairTiles PlusRefinement.bumpy (tile n holes)) := by
  by_cases hg : p ∈ spaceGrid n
  · obtain ⟨q,hq,rfl⟩ := hg
    change (c,1) ∈ q.toVoxel.cells (fun _ => spaceTile n holes) ↔
      c ∈ q.cells (fun _ => tile n holes)
    rw [space_horizontal_cells n holes q.toVoxel rfl]
    simp [sourceHeight,Placement.toVoxel,VoxelPlacement.toPlanar]
  · obtain ⟨a,ha⟩ := meets
    obtain ⟨hk,horizontal⟩ := space_nongrid_middle_small hn period holes admissible
      placements tiling grid p hp hg a ha
    have eq : p.cells (spaceFamily n holes) = p.untag.cells (fun _ => Polycube.bumpyThree) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk]
    have middle := ((Polycube.bumpyThree_horizontal_cells p.untag horizontal (a,1)).mp
      (eq ▸ ha)).2
    rw [eq,Polycube.bumpyThree_horizontal_cells p.untag horizontal]
    simp only [middle,and_true]
    simp [VoxelPlacement.toPlanar,VoxelPlacement.untag,Placement.cells,pairTiles,hk]

theorem planar_tileable_of_space_grid {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements) :
    Tileable (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ := by
  let middle : Set (VoxelPlacement Bool) :=
    {p | p ∈ placements ∧ ∃ a : Cell, (a,1) ∈ p.cells (spaceFamily n holes)}
  refine ⟨VoxelPlacement.toPlanar '' middle,?_,?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨p,⟨hp,hc⟩,unique⟩ := tiling.uniqueCover (c,1) (Set.mem_univ _)
    have meets : ∃ a : Cell, (a,1) ∈ p.cells (spaceFamily n holes) := ⟨c,hc⟩
    refine ⟨p.toPlanar,⟨⟨p,⟨hp,meets⟩,rfl⟩,?_⟩,?_⟩
    · exact (space_middle_slice hn period holes admissible placements tiling grid p hp meets c).mp hc
    · rintro _ ⟨⟨q,⟨hq,mq⟩,rfl⟩,hqc⟩
      exact congrArg VoxelPlacement.toPlanar (unique q ⟨hq,
        (space_middle_slice hn period holes admissible placements tiling grid q hq mq c).mpr hqc⟩)

/-- No seed, orientation, grid, or slab assumption remains. -/
theorem planar_tileable_of_space {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (spaceFamily n holes) Set.univ) :
    Tileable (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ := by
  obtain ⟨ps,ht,grid⟩ := space_tileable_has_grid hn period holes admissible tileable
  exact planar_tileable_of_space_grid hn period holes admissible ps ht grid

end LeanTrominoes.KeyedPeriodicComplement
