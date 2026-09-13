/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSymmetryGroup
import LeanTrominoes.PolycubeSpaceLockData

/-! # Turning relative occupied witnesses into placement obstructions -/

namespace LeanTrominoes

theorem VoxelPlacement.cover_relative {ι : Type*} (tiles : ι → Polycube)
    (p : VoxelPlacement ι) (q c d : Voxel)
    (cover : Voxel.add p.offset (p.symmetry.act q) = c)
    (member : Voxel.add q (p.symmetry.inverseAct d) ∈ tiles p.kind) :
    Voxel.add c d ∈ p.cells tiles := by
  rw [VoxelPlacement.mem_cells_iff]
  refine ⟨_, member, ?_⟩
  rw [CubeSymmetry.act_add, CubeSymmetry.act_inverse_act, ← cover]
  simp only [Voxel.add, Cell.add, Int.add_assoc]

theorem SpaceLock.ForcedOverlap.obstructs {ι : Type*} (tiles : ι → Polycube)
    (p : VoxelPlacement ι) (shape : Polycube) (offsets : Finset Voxel)
    (forced : SpaceLock.ForcedOverlap shape offsets p.symmetry)
    (anchor q c : Voxel) (source : q ∈ shape)
    (embed : ∀ r ∈ shape, Voxel.add anchor r ∈ tiles p.kind)
    (cover : Voxel.add p.offset (p.symmetry.act (Voxel.add anchor q)) = c)
    (obstacle : Polycube) (occupied : ∀ d ∈ offsets, Voxel.add c d ∈ obstacle) :
    ¬ Disjoint obstacle (p.cells tiles) := by
  intro disjoint
  obtain ⟨d, hd, hit⟩ := forced q source
  have member : Voxel.add (Voxel.add anchor q) (p.symmetry.inverseAct d) ∈ tiles p.kind := by
    simpa only [Voxel.add, Cell.add, Int.add_assoc] using embed _ hit
  exact Finset.disjoint_left.mp disjoint (occupied d hd)
    (p.cover_relative tiles _ c d cover member)

end LeanTrominoes
