/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeExtrusion
import LeanTrominoes.KeyedComplementRefinedExclusion

/-! # Finite span and middle-square certificates for full-space recovery -/

namespace LeanTrominoes.Polycube

def spaceCapProbes : Polycube := {((0,0),-1),((4,0),-1),((0,4),-1),((0,0),3)}

theorem spaceCapProbes_span : ∀ s : CubeSymmetry,
    ∃ a ∈ spaceCapProbes, ∃ b ∈ spaceCapProbes, (s.act a).2 + 4 ≤ (s.act b).2 := by
  decide +kernel

/-- An upright small tile either spans at least four layers, or contains a
solid middle square together with a voxel immediately above and below it. -/
theorem bumpyThree_upright_square : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    (∃ a ∈ bumpyThree, ∃ b ∈ bumpyThree, (s.act a).2 + 3 ≤ (s.act b).2) ∨
    (∃ r ∈ bumpyThree.image s.act,
      (r.1,r.2-1) ∈ bumpyThree.image s.act ∧
      (r.1,r.2+1) ∈ bumpyThree.image s.act ∧
      ∀ d ∈ PlusRefinement.unitSquare, (Cell.add r.1 d,r.2) ∈ bumpyThree.image s.act) := by
  decide +kernel

end LeanTrominoes.Polycube
