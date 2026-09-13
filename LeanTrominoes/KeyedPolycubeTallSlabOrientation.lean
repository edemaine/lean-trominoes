/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabGeometry
import LeanTrominoes.KeyedPolycubeSpaceSlices

/-! # A sufficiently wide solid cap fixes background orientation and height -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tallSlabTile_horizontal {height n : Nat} (hh : 3 ≤ height) (wide : height < n)
    (holes : Polyomino) (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => tallSlabTile height n holes), c ∈ voxelSlab height) :
    p.symmetry.axis = 0 := by
  have body := slabBodyHeight_bounds hh
  have cap (c : Cell) (hc : c ∈ square n) : (c,(slabBodyHeight height : Int)) ∈ tallSlabTile height n holes :=
    (mem_tallSlabTile height n holes _).mpr (Or.inr ⟨hc,by omega⟩)
  have bounds (c : Cell) (hc : c ∈ square n) := inside _
    ((p.mem_cells_iff _ _).mpr ⟨(c,(slabBodyHeight height : Int)),cap c hc,rfl⟩)
  have zero := bounds (0,0) (by simp [mem_square]; omega)
  have x := bounds ((height : Int),0) (by simp [mem_square]; omega)
  have y := bounds (0,(height : Int)) (by simp [mem_square]; omega)
  by_contra upright
  rcases hs : p.symmetry with ⟨s,f,a⟩
  fin_cases a <;> cases s <;> cases f <;>
    simp_all [voxelSlab,Voxel.add,CubeSymmetry.act,CubeSymmetry.cycle,SquareSymmetry.act] <;> omega

theorem tallSlabTile_vertical_offset {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => tallSlabTile height n holes), c ∈ voxelSlab height) :
    p.offset.2 = if p.symmetry.flip then (height : Int)-1 else 0 := by
  have horizontal := tallSlabTile_horizontal hh wide holes p inside
  have body := slabBodyHeight_bounds hh
  have origin : (0,0) ∈ tile n holes := lower_tile hn holes admissible (by
    simp [KeyCornerArithmetic.lower,KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock,KeyCornerArithmetic.inHorizontalLock]
    omega)
  have bottom : ((0,0),0) ∈ tallSlabTile height n holes :=
    (mem_tallSlabTile height n holes _).mpr (Or.inl ⟨origin,by omega⟩)
  have top : ((0,0),(height : Int)-1) ∈ tallSlabTile height n holes :=
    (mem_tallSlabTile height n holes _).mpr (Or.inr ⟨by simp [mem_square]; omega,by omega⟩)
  have lo := inside _ ((p.mem_cells_iff _ _).mpr ⟨((0,0),0),bottom,rfl⟩)
  have hi := inside _ ((p.mem_cells_iff _ _).mpr ⟨((0,0),(height : Int)-1),top,rfl⟩)
  cases hf : p.symmetry.flip <;>
    simp [voxelSlab,Voxel.add,CubeSymmetry.act,horizontal,CubeSymmetry.cycle,hf] at * <;> omega

theorem tall_horizontal_cells (height n : Nat) (holes : Polyomino) (p : VoxelPlacement Unit)
    (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun _ => tallSlabTile height n holes) ↔
      (c.1 ∈ p.toPlanar.cells (fun _ => tile n holes) ∧
        0 ≤ sourceHeight p c.2 ∧ sourceHeight p c.2 < slabBodyHeight height) ∨
      (c.1 ∈ p.toPlanar.cells (fun _ => square n) ∧
        (slabBodyHeight height : Int) ≤ sourceHeight p c.2 ∧ sourceHeight p c.2 < height) := by
  rw [VoxelPlacement.mem_cells_inverse,mem_tallSlabTile]
  simp only [cells_source_iff]
  simp [CubeSymmetry.inverseAct,horizontal,CubeSymmetry.cycle,Voxel.sub,
    VoxelPlacement.toPlanar,KeyCornerArithmetic.source,sourceHeight]

end LeanTrominoes.KeyedPeriodicComplement
