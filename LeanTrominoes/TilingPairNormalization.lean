/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingPair
import LeanTrominoes.TilingSymmetry

/-! # Normalizing a distinguished tile in a mixed plane tiling -/

namespace LeanTrominoes

/-- If P cannot tile alone, a rigid change of coordinates puts one Q at the
origin in its original orientation. -/
theorem tileable_pair_normalize (p q : Polyomino) (obstruction : ¬ TileableBy p Set.univ)
    (tileable : Tileable (pairTiles p q) Set.univ) :
    ∃ ps, IsTiling (pairTiles p q) Set.univ ps ∧
      (⟨true, .identity, (0, 0)⟩ : Placement Bool) ∈ ps := by
  obtain ⟨ps, tiling⟩ := tileable
  obtain ⟨a, ha, hk⟩ := right_tile_occurs p q ps tiling obstruction
  refine ⟨{b | (b.orient a.symmetry).shift a.offset ∈ ps},
    (tiling.recenter a.offset).reorient a.symmetry, ?_⟩
  have eq : ((⟨true, .identity, (0, 0)⟩ : Placement Bool).orient a.symmetry).shift a.offset = a := by
    apply Placement.ext
    · exact hk.symm
    · exact SquareSymmetry.compose_identity a.symmetry
    · simp only [Placement.shift, Placement.orient, SquareSymmetry.act_zero,
        Cell.add, Int.add_zero, Prod.eta]
  change _ ∈ ps
  rwa [eq]

end LeanTrominoes
