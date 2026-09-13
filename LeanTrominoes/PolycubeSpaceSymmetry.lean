/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSymmetryGroup
import LeanTrominoes.PolycubeSlabSymmetry

/-! # Normalizing an arbitrary placement in a full-space voxel tiling -/

namespace LeanTrominoes
namespace VoxelPlacement

noncomputable def transform {ι : Type*} (s : CubeSymmetry) (p : VoxelPlacement ι) : VoxelPlacement ι :=
  ⟨p.kind, s.comp p.symmetry, s.act p.offset⟩

@[simp] theorem transform_inverse_cancel {ι : Type*} (s : CubeSymmetry) (p : VoxelPlacement ι) :
    (p.transform s).transform s.inverse = p := by
  apply VoxelPlacement.ext
  · rfl
  · exact CubeSymmetry.inverse_comp_cancel _ _
  · exact (CubeSymmetry.inverse_act _ _).trans (s.inverse_act_act _)

@[simp] theorem inverse_transform_cancel {ι : Type*} (s : CubeSymmetry) (p : VoxelPlacement ι) :
    (p.transform s.inverse).transform s = p := by
  apply VoxelPlacement.ext
  · rfl
  · exact CubeSymmetry.comp_inverse_cancel _ _
  · change s.act (s.inverse.act p.offset) = p.offset
    rw [CubeSymmetry.inverse_act, CubeSymmetry.act_inverse_act]

noncomputable def transformEquiv {ι : Type*} (s : CubeSymmetry) :
    VoxelPlacement ι ≃ VoxelPlacement ι where
  toFun := transform s
  invFun := transform s.inverse
  left_inv := transform_inverse_cancel s
  right_inv := inverse_transform_cancel s

theorem mem_transform_cells {ι : Type*} (tiles : ι → Polycube) (s : CubeSymmetry)
    (p : VoxelPlacement ι) (c : Voxel) :
    s.act c ∈ (p.transform s).cells tiles ↔ c ∈ p.cells tiles := by
  simp only [mem_cells_iff, transform, CubeSymmetry.comp_act, ← CubeSymmetry.act_add,
    (CubeSymmetry.act_injective s).eq_iff]

end VoxelPlacement

theorem IsVoxelTiling.reorient_space {ι : Type*} {tiles : ι → Polycube}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles Set.univ placements)
    (s : CubeSymmetry) : IsVoxelTiling tiles Set.univ {p | p.transform s ∈ placements} := by
  apply tiling.pullback s.voxelEquiv (VoxelPlacement.transformEquiv s)
  · intro c
    rfl
  · intro p _ c
    exact p.mem_transform_cells tiles s c

/-- Any selected placement can be moved to the origin with identity orientation. -/
theorem IsVoxelTiling.normalize_space {ι : Type*} {tiles : ι → Polycube}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles Set.univ placements)
    (p : VoxelPlacement ι) (member : p ∈ placements) :
    ∃ ps, IsVoxelTiling tiles Set.univ ps ∧
      (⟨p.kind, CubeSymmetry.identity, ((0, 0), 0)⟩ : VoxelPlacement ι) ∈ ps := by
  let shifted := tiling.recenter p.offset (by intro c; rfl)
  refine ⟨_, shifted.reorient_space p.symmetry, ?_⟩
  change ((⟨p.kind, CubeSymmetry.identity, ((0, 0), 0)⟩ : VoxelPlacement ι).transform p.symmetry).shift
    p.offset ∈ placements
  have zero : p.symmetry.act ((0, 0), 0) = ((0, 0), 0) := by
    rw [CubeSymmetry.act_basis_expansion]
    simp [Voxel.add, Voxel.scale, Cell.add, Cell.scale]
  simpa [VoxelPlacement.transform, VoxelPlacement.shift, zero, Voxel.add, Cell.add] using member

end LeanTrominoes
