/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSlabSlices
import LeanTrominoes.SlabCapObstruction
import LeanTrominoes.KeyedComplementRightNeighbor

/-! # The two locks force equally oriented neighbors in the height-two slab -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- Transfer local planar forcing to a slab. A downward-facing cap cannot
cover the lock, so the forced background copy also has its cap on top. -/
theorem slab_candidate {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (lock : Cell) (expected : Placement Bool)
    (expected_background : expected.kind = true)
    (forcing : ∀ a : Placement Bool,
      lock ∈ a.cells (planarFamily n holes) →
        Disjoint (tile n holes) (a.cells (planarFamily n holes)) → a = expected)
    (cap : ∀ a : Placement Unit, lock ∈ a.cells (fun _ => square n) →
      ¬ Disjoint (tile n holes) (a.cells (fun _ => square n)))
    (p : VoxelPlacement Bool)
    (inside : ∀ c ∈ p.cells (slabFamily n holes), c ∈ voxelSlab 2)
    (covers : (lock, 0) ∈ p.cells (slabFamily n holes))
    (hd : Disjoint (slabTile n holes) (p.cells (slabFamily n holes))) :
    p = expected.toVoxel := by
  have horizontal := mixed_slab_horizontal hn holes p inside
  cases hk : p.kind with
  | false =>
    obtain ⟨hc, hz⟩ := (small_zero_slice n holes p hk horizontal lock).mp covers
    have disjoint := disjoint_zero_slice n holes p hd
      (p.toPlanar.cells (planarFamily n holes)) (fun c hc =>
        (small_zero_slice n holes p hk horizontal c).mpr ⟨hc, hz⟩)
    have he := congrArg Placement.kind (forcing p.toPlanar hc disjoint)
    simp [VoxelPlacement.toPlanar, hk, expected_background] at he
  | true =>
    have slice := background_zero_slice hn holes admissible p hk inside
    cases hf : p.symmetry.flip with
    | true =>
      have hc : lock ∈ p.toPlanar.untag.cells (fun _ => square n) := by
        simpa [hf] using (slice lock).mp covers
      have disjoint := disjoint_zero_slice n holes p hd
        (p.toPlanar.untag.cells (fun _ => square n)) (fun c hc =>
          (slice c).mpr (by simpa [hf] using hc))
      exact False.elim (cap p.toPlanar.untag hc disjoint)
    | false =>
      have hc : lock ∈ p.toPlanar.cells (planarFamily n holes) := by
        simpa [hf] using (slice lock).mp covers
      have disjoint := disjoint_zero_slice n holes p hd
        (p.toPlanar.cells (planarFamily n holes)) (fun c hc =>
          (slice c).mpr (by simpa [hf] using hc))
      have he := forcing p.toPlanar hc disjoint
      have hz : p.offset.2 = 0 := by
        simpa [hf] using mixed_background_height hn holes admissible p hk inside
      rw [← p.toVoxel_toPlanar horizontal hf hz, he]

def slabReference : VoxelPlacement Bool := referencePlacement.toVoxel

theorem slabReference_cells (n : Nat) (holes : Polyomino) :
    slabReference.cells (slabFamily n holes) = slabTile n holes := by
  simp [slabReference, referencePlacement, Placement.toVoxel, VoxelPlacement.cells,
    slabFamily, Polycube.pairTiles, CubeSymmetry.act, CubeSymmetry.cycle,
    SquareSymmetry.act, Voxel.add, Cell.add]

private theorem neighbor_of_lock {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (lock : Cell) (outside : lock ∉ tile n holes)
    (expected : Placement Bool) (expected_background : expected.kind = true)
    (forcing : ∀ a : Placement Bool, lock ∈ a.cells (planarFamily n holes) →
      Disjoint (tile n holes) (a.cells (planarFamily n holes)) → a = expected)
    (cap : ∀ a : Placement Unit, lock ∈ a.cells (fun _ => square n) →
      ¬ Disjoint (tile n holes) (a.cells (fun _ => square n)))
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (seed : slabReference ∈ placements) : expected.toVoxel ∈ placements := by
  obtain ⟨p, hp, hc⟩ := tiling.exists_cover (c := (lock, 0)) (by
    change 0 ≤ (0 : Int) ∧ (0 : Int) < 2
    decide)
  have distinct : slabReference ≠ p := by
    rintro rfl
    rw [slabReference_cells] at hc
    exact outside (by simpa [slabTile] using hc)
  have hd := tiling.disjoint_cells seed hp distinct
  rw [slabReference_cells] at hd
  have he := slab_candidate hn holes admissible lock expected expected_background
    forcing cap p (tiling.tilesInside p hp) hc hd
  rwa [← he]

theorem slab_vertical_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (seed : slabReference ∈ placements) :
    (⟨true, .identity, (0, -(n : Int))⟩ : Placement Bool).toVoxel ∈ placements := by
  apply neighbor_of_lock hn holes admissible (2, 3) ?_ _ rfl
    (vertical_candidate hn period holes admissible)
    (square_cannot_fill_vertical_lock hn holes admissible) placements tiling seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper, KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
    KeyCornerArithmetic.inKey] at h
  omega

theorem slab_right_neighbor {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (seed : slabReference ∈ placements) :
    (⟨true, .identity, ((n : Int), 0)⟩ : Placement Bool).toVoxel ∈ placements := by
  apply neighbor_of_lock hn holes admissible ((n : Int) - 4, 2) ?_ _ rfl
    (right_candidate hn period holes admissible)
    (square_cannot_fill_right_lock hn holes admissible) placements tiling seed
  intro hc
  have h := tile_upper hn holes hc
  simp [KeyCornerArithmetic.upper, KeyCornerArithmetic.inBox,
    KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
    KeyCornerArithmetic.inKey] at h
  omega

end LeanTrominoes.KeyedPeriodicComplement
