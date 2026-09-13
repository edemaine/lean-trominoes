/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabNormalization
import LeanTrominoes.KeyedPolycubeSpaceMiddle

/-! # A full cap grid confines all nongrid tiles to the simulation layers -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_grid_cap_cover {height n : Nat} (hn : 0 < n) (holes : Polyomino)
    (c : Cell) (z : Int) (hz : (slabBodyHeight height : Int) ≤ z ∧ z < height) :
    ∃ g ∈ spaceGrid n, (c,z) ∈ g.cells (tallSlabFamily height n holes) := by
  obtain ⟨p,hp,hc⟩ := (square_grid_tiling hn).exists_cover (Set.mem_univ c)
  refine ⟨(p.tag true).toVoxel,⟨p,hp,rfl⟩,?_⟩
  change (c,z) ∈ p.toVoxel.cells (fun _ => tallSlabTile height n holes)
  rw [tall_horizontal_cells height n holes p.toVoxel rfl]
  exact Or.inr ⟨hc,by simpa [sourceHeight,Placement.toVoxel] using hz⟩

theorem tall_nongrid_confined {height n : Nat} (hn : 0 < n) (holes : Polyomino)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (grid : ∀ q ∈ gridPlacements n, (q.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (nongrid : p ∉ spaceGrid n) :
    ∀ c ∈ p.cells (tallSlabFamily height n holes), 0 ≤ c.2 ∧ c.2 < slabBodyHeight height := by
  intro c hc
  have bounds := tiling.tilesInside p hp c hc
  refine ⟨bounds.1,?_⟩
  by_contra outside
  obtain ⟨g,⟨q,hq,eq⟩,hg⟩ := tall_grid_cap_cover hn holes c.1 c.2 ⟨by omega,bounds.2⟩
  have member : g ∈ placements := eq ▸ grid q hq
  have distinct : p ≠ g := by rintro rfl; exact nongrid ⟨q,hq,eq⟩
  exact Finset.disjoint_left.mp (tiling.disjoint_cells hp member distinct) hc hg

theorem tall_background_not_confined {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (p : VoxelPlacement Unit) :
    ¬ ∀ c ∈ p.cells (fun _ => tallSlabTile height n holes), 0 ≤ c.2 ∧ c.2 < slabBodyHeight height := by
  intro confined
  have body := slabBodyHeight_bounds hh
  have inside : ∀ c ∈ p.cells (fun _ => tallSlabTile height n holes), c ∈ voxelSlab height := by
    intro c hc
    have := confined c hc
    change 0 ≤ c.2 ∧ c.2 < height
    omega
  have horizontal := tallSlabTile_horizontal hh wide holes p inside
  have origin : (0,0) ∈ tile n holes := lower_tile hn holes admissible (by
    simp [KeyCornerArithmetic.lower,KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock,KeyCornerArithmetic.inHorizontalLock]
    omega)
  have bottom : ((0,0),0) ∈ tallSlabTile height n holes :=
    (mem_tallSlabTile height n holes _).mpr (Or.inl ⟨origin,by omega⟩)
  have top : ((0,0),(height : Int)-1) ∈ tallSlabTile height n holes :=
    (mem_tallSlabTile height n holes _).mpr (Or.inr ⟨by simp [mem_square]; omega,by omega⟩)
  have lo := confined _ ((p.mem_cells_iff _ _).mpr ⟨((0,0),0),bottom,rfl⟩)
  have hi := confined _ ((p.mem_cells_iff _ _).mpr ⟨((0,0),(height : Int)-1),top,rfl⟩)
  cases hf : p.symmetry.flip <;>
    simp [Voxel.add,CubeSymmetry.act,horizontal,CubeSymmetry.cycle,hf] at lo hi <;> omega

end LeanTrominoes.KeyedPeriodicComplement
