/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceSlices

/-! # Horizontal slices of the fixed three-layer small polycube -/

namespace LeanTrominoes.Polycube

theorem bumpyThree_horizontal_cells (p : VoxelPlacement Unit)
    (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun _ => bumpyThree) ↔
      c.1 ∈ p.toPlanar.cells (fun _ => PlusRefinement.bumpy) ∧
      0 ≤ KeyedPeriodicComplement.sourceHeight p c.2 ∧
        KeyedPeriodicComplement.sourceHeight p c.2 ≤ 2 := by
  rw [VoxelPlacement.mem_cells_inverse]
  simp only [bumpyThree,mem_extrude,KeyedPeriodicComplement.cells_source_iff]
  simp [CubeSymmetry.inverseAct,horizontal,CubeSymmetry.cycle,Voxel.sub,
    VoxelPlacement.toPlanar,KeyCornerArithmetic.source,KeyedPeriodicComplement.sourceHeight]
  omega

end LeanTrominoes.Polycube
