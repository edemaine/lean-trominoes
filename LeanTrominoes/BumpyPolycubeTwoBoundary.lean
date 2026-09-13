/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubeTwoCertificates
import LeanTrominoes.PolycubeRelativeObstruction

/-! # A boundary voxel of a thickness-two tile forces the inward voxel -/

namespace LeanTrominoes.Polycube

theorem bumpyTwo_boundary_inward (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => bumpyTwo), c ∈ voxelSlab 3)
    (c : Voxel) (hc : c ∈ p.cells (fun _ => bumpyTwo))
    (boundary : c.2 = 0 ∨ c.2 = 2) :
    (c.1,1) ∈ p.cells (fun _ => bumpyTwo) := by
  obtain ⟨q,hq,eq⟩ := (p.mem_cells_iff _ c).mp hc
  have coord : p.offset.2 + (p.symmetry.act q).2 = c.2 := congrArg Prod.snd eq
  have bounds (r : Voxel) (hr : r ∈ bumpyTwo) :
      0 ≤ p.offset.2 + (p.symmetry.act r).2 ∧ p.offset.2 + (p.symmetry.act r).2 < 3 :=
    inside _ ((p.mem_cells_iff _ _).mpr ⟨r,hr,rfl⟩)
  rcases boundary with hz | hz
  · have minimum : ∀ r ∈ bumpyTwo, (p.symmetry.act q).2 ≤ (p.symmetry.act r).2 := by
      intro r hr
      have := bounds r hr
      omega
    have hit := p.cover_relative (fun _ => bumpyTwo) q c ((0,0),1) eq
      (bumpyTwo_min_inward p.symmetry q hq minimum)
    simpa [Voxel.add,Cell.add,hz] using hit
  · have maximum : ∀ r ∈ bumpyTwo, (p.symmetry.act r).2 ≤ (p.symmetry.act q).2 := by
      intro r hr
      have := bounds r hr
      omega
    have hit := p.cover_relative (fun _ => bumpyTwo) q c ((0,0),-1) eq
      (bumpyTwo_max_inward p.symmetry q hq maximum)
    simpa [Voxel.add,Cell.add,hz] using hit

end LeanTrominoes.Polycube
