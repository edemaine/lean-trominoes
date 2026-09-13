/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubeTwoCertificates
import LeanTrominoes.PolycubeConnectivity

/-! # The thickness-two small tile is connected and cannot stand in two layers -/

namespace LeanTrominoes.Polycube

private theorem upright_span : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    ∃ a ∈ bumpyTwo, ∃ b ∈ bumpyTwo, (s.act a).2 + 2 ≤ (s.act b).2 := by decide +kernel

theorem bumpyTwo_horizontal_in_two_layers (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => bumpyTwo), 0 ≤ c.2 ∧ c.2 < 2) : p.symmetry.axis = 0 := by
  by_contra upright
  obtain ⟨a,ha,b,hb,span⟩ := upright_span p.symmetry upright
  have lo := inside _ ((p.mem_cells_iff _ _).mpr ⟨a,ha,rfl⟩)
  have hi := inside _ ((p.mem_cells_iff _ _).mpr ⟨b,hb,rfl⟩)
  dsimp [Voxel.add] at lo hi
  omega

theorem bumpyTwo_connected : IsConnected bumpyTwo := by
  let previous (c : Voxel) :=
    if c.2 ≠ 0 then (c.1,c.2-1)
    else if c.1.2 ≠ 0 then ((c.1.1,0),0)
    else if c.1.1 > 0 then ((c.1.1-1,0),0) else ((c.1.1+1,0),0)
  let rank (c : Voxel) := c.1.1.natAbs + c.1.2.natAbs + c.2.natAbs
  apply connected_of_predecessor bumpyTwo ((0,0),0) (by decide +kernel) previous rank
  decide +kernel

end LeanTrominoes.Polycube
