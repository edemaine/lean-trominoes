/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceSymmetry

/-! # Normalize a selected placement whenever its affine frame preserves the region -/

namespace LeanTrominoes

def Voxel.shiftEquiv (offset : Voxel) : Voxel ≃ Voxel where
  toFun := Voxel.add offset
  invFun c := Voxel.sub c offset
  left_inv c := by simp [Voxel.add,Voxel.sub,Cell.add,Cell.sub]
  right_inv c := by simp [Voxel.add,Voxel.sub,Cell.add,Cell.sub]

def VoxelPlacement.shiftEquiv {ι : Type*} (offset : Voxel) : VoxelPlacement ι ≃ VoxelPlacement ι where
  toFun := shift offset
  invFun := shift (Voxel.sub ((0,0),0) offset)
  left_inv p := by
    apply VoxelPlacement.ext
    · rfl
    · rfl
    · simp [shift,Voxel.add,Voxel.sub,Cell.add,Cell.sub]
  right_inv := shift_cancel offset

theorem IsVoxelTiling.normalize_preserving {ι : Type*} {tiles : ι → Polycube}
    {region : Set Voxel} {placements : Set (VoxelPlacement ι)}
    (tiling : IsVoxelTiling tiles region placements) (p : VoxelPlacement ι) (hp : p ∈ placements)
    (invariant : ∀ c, Voxel.add p.offset (p.symmetry.act c) ∈ region ↔ c ∈ region) :
    ∃ ps, IsVoxelTiling tiles region ps ∧
      (⟨p.kind,CubeSymmetry.identity,((0,0),0)⟩ : VoxelPlacement ι) ∈ ps := by
  let records : VoxelPlacement ι ≃ VoxelPlacement ι := (VoxelPlacement.transformEquiv p.symmetry).trans (VoxelPlacement.shiftEquiv p.offset)
  let world := p.symmetry.voxelEquiv.trans (Voxel.shiftEquiv p.offset)
  have geometry (q : VoxelPlacement ι) (c : Voxel) :
      world c ∈ (records q).cells tiles ↔ c ∈ q.cells tiles := by
    change Voxel.add p.offset (p.symmetry.act c) ∈ ((q.transform p.symmetry).shift p.offset).cells tiles ↔ _
    rw [VoxelPlacement.mem_shift_cells,VoxelPlacement.mem_transform_cells]
  refine ⟨{q | records q ∈ placements},tiling.pullback world records invariant (fun q _ c => geometry q c),?_⟩
  have zero : p.symmetry.act ((0,0),0) = ((0,0),0) := by
    rw [CubeSymmetry.act_basis_expansion]
    simp [Voxel.add,Voxel.scale,Cell.add,Cell.scale]
  change records ⟨p.kind,CubeSymmetry.identity,((0,0),0)⟩ ∈ placements
  simpa [records,VoxelPlacement.shiftEquiv,VoxelPlacement.transformEquiv,
    VoxelPlacement.transform,VoxelPlacement.shift,zero,Voxel.add,Cell.add] using hp

end LeanTrominoes
