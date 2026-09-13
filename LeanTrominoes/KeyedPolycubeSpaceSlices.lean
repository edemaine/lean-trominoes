/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGeometry
import LeanTrominoes.PolycubeCovering
import LeanTrominoes.PolycubeHorizontalSlice
import LeanTrominoes.KeyedComplementVerticalNeighbor

/-! # Exact slices of horizontal solid-cap background placements -/

namespace LeanTrominoes.KeyedPeriodicComplement

def sourceHeight (p : VoxelPlacement Unit) (z : Int) : Int :=
  if p.symmetry.flip then p.offset.2 - z else z - p.offset.2

theorem space_horizontal_cells (n : Nat) (holes : Polyomino) (p : VoxelPlacement Unit)
    (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun _ => spaceTile n holes) ↔
      (c.1 ∈ p.toPlanar.cells (fun _ => tile n holes) ∧
        0 ≤ sourceHeight p c.2 ∧ sourceHeight p c.2 ≤ 2) ∨
      (c.1 ∈ p.toPlanar.cells (fun _ => square n) ∧
        (sourceHeight p c.2 = -1 ∨ sourceHeight p c.2 = 3)) := by
  rw [VoxelPlacement.mem_cells_inverse, mem_spaceTile]
  simp only [cells_source_iff]
  simp [CubeSymmetry.inverseAct, horizontal, CubeSymmetry.cycle, Voxel.sub,
    VoxelPlacement.toPlanar, KeyCornerArithmetic.source, sourceHeight]

theorem space_background_height (n : Nat) (holes : Polyomino) (p : VoxelPlacement Unit)
    (horizontal : p.symmetry.axis = 0) (c : Cell) (inside : c ∈ square n)
    (planarCover : c ∈ p.toPlanar.cells (fun _ => tile n holes))
    (middle : 0 ≤ sourceHeight p 1 ∧ sourceHeight p 1 ≤ 2)
    (disjoint : Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes))) :
    p.offset.2 = if p.symmetry.flip then 2 else 0 := by
  have absent (z : Int) (hz : z = -1 ∨ z = 3) :
      ¬ (0 ≤ sourceHeight p z ∧ sourceHeight p z ≤ 2) := by
    intro body
    have ref : (c,z) ∈ spaceTile n holes := (mem_spaceTile n holes _).mpr (Or.inr ⟨inside,hz⟩)
    have candidate := (space_horizontal_cells n holes p horizontal (c,z)).mpr
      (Or.inl ⟨planarCover,body⟩)
    exact Finset.disjoint_left.mp disjoint ref candidate
  have bottom := absent (-1) (Or.inl rfl)
  have top := absent 3 (Or.inr rfl)
  cases hf : p.symmetry.flip <;> simp [sourceHeight,hf] at * <;> omega

end LeanTrominoes.KeyedPeriodicComplement
