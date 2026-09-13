/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabCaps
import LeanTrominoes.BumpyPolycubeTwoOrientation

/-! # Nongrid placements are horizontal small tiles -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_grid_body_cover {height n : Nat} (hh : 3 ≤ height) (hn : 0 < n)
    (holes : Polyomino) (c : Cell) (outside : c ∉ holesRegion n holes) :
    ∃ g ∈ spaceGrid n, (c,1) ∈ g.cells (tallSlabFamily height n holes) := by
  obtain ⟨p,hp,hc⟩ := (grid_tiling hn holes).exists_cover outside
  refine ⟨(p.tag true).toVoxel,⟨p,hp,rfl⟩,?_⟩
  change (c,1) ∈ p.toVoxel.cells (fun _ => tallSlabTile height n holes)
  rw [tall_horizontal_cells height n holes p.toVoxel rfl]
  have body := slabBodyHeight_bounds hh
  exact Or.inl ⟨hc,by simp [sourceHeight,Placement.toVoxel]; omega⟩

theorem tall_nongrid_middle_holes {height n : Nat} (hh : 3 ≤ height) (hn : 0 < n)
    (holes : Polyomino) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (grid : ∀ q ∈ gridPlacements n, (q.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n)
    (c : Cell) (hc : (c,1) ∈ p.cells (tallSlabFamily height n holes)) : c ∈ holesRegion n holes := by
  by_contra outside
  obtain ⟨g,⟨q,hq,eq⟩,hg⟩ := tall_grid_body_cover hh hn holes c outside
  have member : g ∈ placements := eq ▸ grid q hq
  have distinct : p ≠ g := by rintro rfl; exact nongrid ⟨q,hq,eq⟩
  exact Finset.disjoint_left.mp (tiling.disjoint_cells hp member distinct) hc hg

theorem tall_nongrid_small_horizontal {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (grid : ∀ q ∈ gridPlacements n, (q.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n) :
    p.kind = false ∧ p.symmetry.axis = 0 := by
  have confined := tall_nongrid_confined (by omega) holes placements tiling grid p hp nongrid
  cases hk : p.kind with
  | true =>
    apply False.elim
    apply tall_background_not_confined hh wide hn holes admissible p.untag
    simpa [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,hk] using confined
  | false =>
    refine ⟨rfl,?_⟩
    have two : height ≠ 2 := by omega
    by_cases three : height = 3
    · apply Polycube.bumpyTwo_horizontal_in_two_layers p.untag
      simpa [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,
        TwoConnectedPolycubes.slabSmall,slabBodyHeight,hk,two,three] using confined
    · apply Polycube.bumpyThree_horizontal_of_cross_slice p.untag
      · have bound : ∀ c ∈ p.untag.cells (fun _ => Polycube.bumpyThree), 0 ≤ c.2 ∧ c.2 < 3 := by
          simpa [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,
            TwoConnectedPolycubes.slabSmall,slabBodyHeight,hk,two,three] using confined
        intro c hc
        have := bound c hc
        omega
      · intro c hc
        apply holesRegion_cross period holes admissible c
        apply tall_nongrid_middle_holes hh (by omega) holes placements tiling grid p hp nongrid c
        simpa [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,
          TwoConnectedPolycubes.slabSmall,hk,two,three] using hc

end LeanTrominoes.KeyedPeriodicComplement
