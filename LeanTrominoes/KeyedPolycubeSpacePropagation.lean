/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceNeighbors
import LeanTrominoes.PolycubeTranslation

/-! # A space background seed forces a complete quadrant of aligned copies -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem space_translated_neighbors {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (canonical : SpaceCanonical placements)
    (offset : Cell)
    (seed : (⟨true, .identity, offset⟩ : Placement Bool).toVoxel ∈ placements) :
    (⟨true, .identity, Cell.add offset (0, -(n : Int))⟩ : Placement Bool).toVoxel ∈ placements ∧
      (⟨true, .identity, Cell.add offset ((n : Int), 0)⟩ : Placement Bool).toVoxel ∈ placements := by
  have reference : spaceReference ∈ {p : VoxelPlacement Bool | p.shift (offset, 0) ∈ placements} := by
    simpa [spaceReference, referencePlacement, Placement.shift, Cell.add] using seed
  have vertical := space_vertical_neighbor hn period holes admissible _ (tiling.recenter (offset,0) (by intro c; simp)) (fun p hp hk ha => canonical (p.shift (offset,0)) hp hk ha) reference
  have right := space_right_neighbor hn period holes admissible _ (tiling.recenter (offset,0) (by intro c; simp)) (fun p hp hk ha => canonical (p.shift (offset,0)) hp hk ha) reference
  simpa only [Set.mem_setOf_eq, VoxelPlacement.shift_toVoxel, Placement.shift] using And.intro vertical right

theorem space_quadrant_placements {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements)
    (canonical : SpaceCanonical placements)
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
      have next := (space_translated_neighbors hn period holes admissible placements tiling canonical _ ih).1
      simpa only [Cell.add, Nat.cast_zero, Int.mul_zero, Int.add_zero, Nat.cast_add,
        Nat.cast_one, Int.mul_add, Int.mul_one, Int.add_assoc] using next
  | succ i ih =>
    have next := (space_translated_neighbors hn period holes admissible placements tiling canonical _ ih).2
    simpa only [Cell.add, Nat.cast_add, Nat.cast_one, Int.mul_add, Int.mul_one,
      Int.add_zero, Int.add_assoc] using next

end LeanTrominoes.KeyedPeriodicComplement
