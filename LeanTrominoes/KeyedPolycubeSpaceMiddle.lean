/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceCaps
import LeanTrominoes.PolycubeSpaceSliceObstructions

/-! # Only horizontal small tiles can fill the holes in the middle layer -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem space_grid_body_cover {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (c : Cell) (outside : c ∉ holesRegion n holes) :
    ∃ g ∈ spaceGrid n, (c,1) ∈ g.cells (spaceFamily n holes) := by
  obtain ⟨p,hp,hc⟩ := (grid_tiling hn holes).exists_cover outside
  refine ⟨(p.tag true).toVoxel,⟨p,hp,rfl⟩,?_⟩
  change (c,1) ∈ p.toVoxel.cells (fun _ => spaceTile n holes)
  rw [space_horizontal_cells n holes p.toVoxel rfl]
  exact Or.inl ⟨hc,by simp [sourceHeight,Placement.toVoxel]⟩

theorem space_nongrid_middle_holes {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n)
    (c : Cell) (hc : (c,1) ∈ p.cells (spaceFamily n holes)) : c ∈ holesRegion n holes := by
  by_contra outside
  obtain ⟨g,⟨q,hq,eq⟩,hg⟩ := space_grid_body_cover hn holes c outside
  have member : g ∈ placements := eq ▸ grid q hq
  have distinct : p ≠ g := by rintro rfl; exact nongrid ⟨q,hq,eq⟩
  exact Finset.disjoint_left.mp (tiling.disjoint_cells hp member distinct) hc hg

theorem holesRegion_cross {n : Nat} (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (c : Cell) (hc : c ∈ holesRegion n holes) : c.1 % 3 = 0 ∨ c.2 % 3 = 0 := by
  have h := (admissible (residue n c) hc).1
  simpa only [residue,Int.emod_emod_of_dvd _ (Int.dvd_of_emod_eq_zero period)] using h

theorem space_nongrid_middle_small {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n)
    (a : Cell) (ha : (a,1) ∈ p.cells (spaceFamily n holes)) :
    p.kind = false ∧ p.symmetry.axis = 0 := by
  have confined := space_nongrid_confined hn holes admissible placements tiling grid p hp nongrid a ha
  cases hk : p.kind with
  | true =>
    apply False.elim
    apply spaceTile_not_confined hn holes p.untag
    simpa [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk] using confined
  | false =>
    refine ⟨rfl,Polycube.bumpyThree_horizontal_of_cross_slice p.untag ?_ ?_⟩
    · simpa [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk] using confined
    · intro c hc
      apply holesRegion_cross period holes admissible c
      apply space_nongrid_middle_holes (by omega) holes placements tiling grid p hp nongrid c
      simpa [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,hk] using hc

end LeanTrominoes.KeyedPeriodicComplement
