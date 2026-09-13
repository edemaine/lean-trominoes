/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPeriodicComplement

/-! # The square caps tile a plane at the canonical background offsets -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem square_grid_tiling {n : Nat} (hn : 0 < n) :
    IsTiling (fun _ : Unit => square n) Set.univ (gridPlacements n) := by
  constructor
  · intro _ _ _ _
    trivial
  · intro c _
    let p : Placement Unit := ⟨(), .identity, Cell.sub c (residue n c)⟩
    have hp : p ∈ gridPlacements n := by
      refine ⟨rfl, c.1 / n, c.2 / n, ?_⟩
      have hx := Int.emod_add_mul_ediv c.1 (n : Int)
      have hy := Int.emod_add_mul_ediv c.2 (n : Int)
      apply Prod.ext <;> dsimp [p, Cell.sub, residue] <;> omega
    have covers : c ∈ p.cells (fun _ => square n) := by
      apply (Placement.mem_cells_iff _ _ _).mpr
      exact ⟨residue n c, residue_mem_square hn c,
        by simp [p, Cell.add, Cell.sub, SquareSymmetry.act]⟩
    refine ⟨p, ⟨hp, covers⟩, ?_⟩
    rintro other ⟨⟨hs, i, j, hoff⟩, hcover⟩
    obtain ⟨r, hr, he⟩ := (Placement.mem_cells_iff _ _ _).mp hcover
    have residueEq : residue n r = residue n c := by
      rw [← he, hs, hoff]
      simp [residue, Cell.add, SquareSymmetry.act, Int.add_emod]
    rw [residue_of_mem_square hr] at residueEq
    subst r
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · exact hs
    · have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      simp only [hs, SquareSymmetry.act, Cell.add] at hx hy
      apply Prod.ext <;> dsimp [p, Cell.sub] <;> omega

end LeanTrominoes.KeyedPeriodicComplement
