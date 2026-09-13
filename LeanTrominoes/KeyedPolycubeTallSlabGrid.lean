/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabPropagation
import LeanTrominoes.PolycubePrescribedCompactness
import Mathlib.Tactic.Ring

/-! # A slab tiling containing the complete canonical Q grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

private def tallGridPatch (n r : Nat) : Set (VoxelPlacement Bool) :=
  {p | ∃ i j : Int, -(r : Int) ≤ i ∧ i ≤ r ∧ -(r : Int) ≤ j ∧ j ≤ r ∧
    p = (⟨true, .identity, ((n : Int) * i, (n : Int) * j)⟩ : Placement Bool).toVoxel}

/-- Compactness converts the forced quadrant into a new mixed tiling with
every canonical Q placement present. -/
theorem tall_slab_exists_tiling_with_grid {height n : Nat} (hh : 3 ≤ height) (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) placements)
    (seed : tallSlabReference ∈ placements) :
    ∃ ps, IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) ps ∧
      ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ ps := by
  have increasing : ∀ r, tallGridPatch n r ⊆ tallGridPatch n (r + 1) := by
    rintro r p ⟨i, j, hi₀, hi₁, hj₀, hj₁, hp⟩
    exact ⟨i, j, by omega, by omega, by omega, by omega, hp⟩
  have realized : ∀ r, ∃ ps,
      IsVoxelTiling (tallSlabFamily height n holes) (voxelSlab height) ps ∧
        tallGridPatch n r ⊆ ps := by
    intro r
    let offset : Cell := ((n : Int) * r, -(n : Int) * r)
    refine ⟨{p | p.shift (offset, 0) ∈ placements}, tiling.recenter_slab offset, ?_⟩
    rintro p ⟨i, j, hi₀, hi₁, hj₀, hj₁, rfl⟩
    have hi : (((r : Int) + i).toNat : Int) = (r : Int) + i := by omega
    have hj : (((r : Int) - j).toNat : Int) = (r : Int) - j := by omega
    have forced := tall_slab_quadrant_placements hh wide hn period holes admissible placements tiling
      (0, 0) seed ((r : Int) + i).toNat ((r : Int) - j).toNat
    have eq : (⟨true, .identity, ((n : Int) * i, (n : Int) * j)⟩ : Placement Bool).toVoxel.shift (offset, 0) =
        (⟨true, .identity,
          Cell.add (0, 0) ((n : Int) * ((r : Int) + i).toNat,
            -(n : Int) * ((r : Int) - j).toNat)⟩ : Placement Bool).toVoxel := by
      rw [VoxelPlacement.shift_toVoxel]
      apply congrArg Placement.toVoxel
      apply Placement.ext
      · rfl
      · rfl
      · apply Prod.ext <;> dsimp [Placement.shift, offset, Cell.add] <;>
          simp only [hi, hj] <;> ring
    change _ ∈ placements
    rwa [eq]
  obtain ⟨ps, ht, patches⟩ := VoxelTilingSelection.exists_tiling_of_prescriptions
    (tallSlabFamily height n holes) (voxelSlab height) (tallGridPatch n) increasing realized
  refine ⟨ps, ht, ?_⟩
  rintro p ⟨hs, i, j, hp⟩
  apply patches (max i.natAbs j.natAbs)
  refine ⟨i, j, ?_, ?_, ?_, ?_, ?_⟩
  · have : -(i.natAbs : Int) ≤ i := by simpa [Int.natCast_natAbs] using neg_abs_le i
    have := Nat.le_max_left i.natAbs j.natAbs
    omega
  · have : i ≤ (i.natAbs : Int) := Int.le_natAbs
    have := Nat.le_max_left i.natAbs j.natAbs
    omega
  · have : -(j.natAbs : Int) ≤ j := by simpa [Int.natCast_natAbs] using neg_abs_le j
    have := Nat.le_max_right i.natAbs j.natAbs
    omega
  · have : j ≤ (j.natAbs : Int) := Int.le_natAbs
    have := Nat.le_max_right i.natAbs j.natAbs
    omega
  · exact congrArg Placement.toVoxel (Placement.ext rfl hs hp)

end LeanTrominoes.KeyedPeriodicComplement
