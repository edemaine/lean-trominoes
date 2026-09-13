/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabRecoveryOrientation

/-! # Exact planar footprints in a taller-slab tiling with its cap grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_small_horizontal_cells {height : Nat} (hh : 3 ≤ height)
    (p : VoxelPlacement Unit) (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height) ↔
      c.1 ∈ p.toPlanar.cells (fun _ => PlusRefinement.bumpy) ∧
      0 ≤ sourceHeight p c.2 ∧ sourceHeight p c.2 < slabBodyHeight height := by
  rw [VoxelPlacement.mem_cells_inverse,slabSmall_eq_extrude hh]
  simp only [Polycube.mem_extrude,Finset.mem_Ico,cells_source_iff]
  simp [CubeSymmetry.inverseAct,horizontal,CubeSymmetry.cycle,Voxel.sub,
    VoxelPlacement.toPlanar,KeyCornerArithmetic.source,sourceHeight]

theorem tall_small_confined_offset {height : Nat} (hh : 3 ≤ height)
    (p : VoxelPlacement Unit) (horizontal : p.symmetry.axis = 0)
    (confined : ∀ c ∈ p.cells (fun _ => TwoConnectedPolycubes.slabSmall height),
      0 ≤ c.2 ∧ c.2 < slabBodyHeight height) :
    p.offset.2 = if p.symmetry.flip then (slabBodyHeight height : Int)-1 else 0 := by
  have body := slabBodyHeight_bounds hh
  have member (z : Int) (hz : 0 ≤ z ∧ z < slabBodyHeight height) :
      ((0,0),z) ∈ TwoConnectedPolycubes.slabSmall height := by
    rw [slabSmall_eq_extrude hh]
    simp [Polycube.mem_extrude,PlusRefinement.origin_mem_bumpy,hz]
  have lo := confined _ ((p.mem_cells_iff _ _).mpr ⟨((0,0),0),member 0 (by omega),rfl⟩)
  have hi := confined _ ((p.mem_cells_iff _ _).mpr
    ⟨((0,0),(slabBodyHeight height : Int)-1),member _ (by omega),rfl⟩)
  cases hf : p.symmetry.flip <;>
    simp [Voxel.add,CubeSymmetry.act,horizontal,CubeSymmetry.cycle,hf] at * <;> omega

theorem tall_slab_middle_slice {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (grid : ∀ q ∈ gridPlacements n, (q.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (c : Cell) :
    (c,1) ∈ p.cells (tallSlabFamily height n holes) ↔
      c ∈ p.toPlanar.cells (pairTiles PlusRefinement.bumpy (tile n holes)) := by
  have body := slabBodyHeight_bounds hh
  by_cases hg : p ∈ spaceGrid n
  · obtain ⟨q,hq,rfl⟩ := hg
    change (c,1) ∈ q.toVoxel.cells (fun _ => tallSlabTile height n holes) ↔
      c ∈ q.cells (fun _ => tile n holes)
    rw [tall_horizontal_cells height n holes q.toVoxel rfl]
    simp [sourceHeight,Placement.toVoxel,VoxelPlacement.toPlanar,show (1 : Int) < slabBodyHeight height by omega,show ¬slabBodyHeight height ≤ 1 by omega]
  · obtain ⟨hk,horizontal⟩ := tall_nongrid_small_horizontal hh wide hn period holes admissible
      placements tiling grid p hp hg
    have eq : p.cells (tallSlabFamily height n holes) = p.untag.cells (fun _ => TwoConnectedPolycubes.slabSmall height) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,tallSlabFamily,Polycube.pairTiles,hk]
    have confined := tall_nongrid_confined (by omega) holes placements tiling grid p hp hg
    rw [eq] at confined
    have heightEq := tall_small_confined_offset hh p.untag horizontal confined
    have middle : 0 ≤ sourceHeight p.untag 1 ∧ sourceHeight p.untag 1 < slabBodyHeight height := by
      cases hf : p.symmetry.flip <;> simp [sourceHeight,VoxelPlacement.untag,hf] at * <;> omega
    rw [eq,tall_small_horizontal_cells hh p.untag horizontal]
    simp only [middle,and_true]
    simp [VoxelPlacement.toPlanar,VoxelPlacement.untag,Placement.cells,pairTiles,hk]

end LeanTrominoes.KeyedPeriodicComplement
