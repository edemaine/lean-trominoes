/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabLocks
import LeanTrominoes.PolycubeTranslation

/-! # A slab background seed forces a complete quadrant of aligned copies -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_slab_translated_neighbors {height n : Nat} (hh : 3 ≤ height) (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (offset : Cell)
    (seed : (⟨true, .identity, offset⟩ : Placement Bool).toVoxel ∈ placements) :
    (⟨true, .identity, Cell.add offset (0, -(n : Int))⟩ : Placement Bool).toVoxel ∈ placements ∧
      (⟨true, .identity, Cell.add offset ((n : Int), 0)⟩ : Placement Bool).toVoxel ∈ placements := by
  have reference : tallSlabReference ∈ {p : VoxelPlacement Bool | p.shift (offset, 0) ∈ placements} := by
    simpa [tallSlabReference, referencePlacement, Placement.shift, Cell.add] using seed
  have vertical := tall_slab_vertical_neighbor hh wide hn period holes admissible _ (tiling.recenter_slab offset) reference
  have right := tall_slab_right_neighbor hh wide hn period holes admissible _ (tiling.recenter_slab offset) reference
  simpa only [Set.mem_setOf_eq, VoxelPlacement.shift_toVoxel, Placement.shift] using And.intro vertical right

theorem tall_slab_quadrant_placements {height n : Nat} (hh : 3 ≤ height) (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (offset : Cell)
    (seed : (⟨true, .identity, offset⟩ : Placement Bool).toVoxel ∈ placements)
    (i j : Nat) :
    (⟨true, .identity,
      Cell.add offset ((n : Int) * i, -(n : Int) * j)⟩ : Placement Bool).toVoxel ∈ placements := by
  induction i with
  | zero =>
    induction j with
    | zero => simpa [Cell.add] using seed
    | succ j ih =>
      have next := (tall_slab_translated_neighbors hh wide hn period holes admissible placements tiling _ ih).1
      simpa only [Cell.add, Nat.cast_zero, Int.mul_zero, Int.add_zero, Nat.cast_add,
        Nat.cast_one, Int.mul_add, Int.mul_one, Int.add_assoc] using next
  | succ i ih =>
    have next := (tall_slab_translated_neighbors hh wide hn period holes admissible placements tiling _ ih).2
    simpa only [Cell.add, Nat.cast_add, Nat.cast_one, Int.mul_add, Int.mul_one,
      Int.add_zero, Int.add_assoc] using next

end LeanTrominoes.KeyedPeriodicComplement
