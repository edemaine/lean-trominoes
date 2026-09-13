/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeExtrusion

/-! # Boundary and pocket certificates for the exceptional height-three slab -/

namespace LeanTrominoes.Polycube

def bumpyTwo : Polycube := extrude PlusRefinement.bumpy {0,1}

theorem bumpyTwo_card : bumpyTwo.card = 30 := by decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem bumpyTwo_min_inward : ∀ s : CubeSymmetry, ∀ q ∈ bumpyTwo,
    (∀ r ∈ bumpyTwo, (s.act q).2 ≤ (s.act r).2) →
      Voxel.add q (s.inverseAct ((0,0),1)) ∈ bumpyTwo := by decide +kernel

theorem bumpyTwo_max_inward : ∀ s : CubeSymmetry, ∀ q ∈ bumpyTwo,
    (∀ r ∈ bumpyTwo, (s.act r).2 ≤ (s.act q).2) →
      Voxel.add q (s.inverseAct ((0,0),-1)) ∈ bumpyTwo := by decide +kernel

theorem bumpyTwo_upright_pocket : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    (∃ a ∈ bumpyTwo, ∃ b ∈ bumpyTwo, (s.act a).2 + 3 ≤ (s.act b).2) ∨
    (((s.act ((1,1),0)).2 = (s.act ((0,-1),0)).2 ∨
      (s.act ((1,1),0)).2 = (s.act ((0,1),0)).2) ∧
    ((s.act ((0,-1),0)).2 + 2 = (s.act ((0,1),0)).2 ∨
      (s.act ((0,1),0)).2 + 2 = (s.act ((0,-1),0)).2) ∧
    (s.act ((1,0),0)).1 = (s.act ((1,1),0)).1 ∧
    2 * (s.act ((1,0),0)).2 =
      (s.act ((0,-1),0)).2 + (s.act ((0,1),0)).2) := by decide +kernel

end LeanTrominoes.Polycube
