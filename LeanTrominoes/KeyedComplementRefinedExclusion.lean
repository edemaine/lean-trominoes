/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementEnvelope
import LeanTrominoes.PlusRefinementGeometry

/-! # A keyed background tile cannot hide inside the refined holes -/

namespace LeanTrominoes.PlusRefinement

def unitSquare : Polyomino := {(0, 0), (1, 0), (0, 1), (1, 1)}

/-- No refined region contains a solid 2-by-2 block, in any orientation. -/
theorem no_oriented_unitSquare (original : Set Cell) (s : SquareSymmetry) (offset : Cell) :
    ¬ ∀ c ∈ unitSquare, Cell.add offset (s.act c) ∈ region original := by
  intro h
  have a := region_mod_three (h (0, 0) (by decide))
  have b := region_mod_three (h (1, 0) (by decide))
  have c := region_mod_three (h (0, 1) (by decide))
  have d := region_mod_three (h (1, 1) (by decide))
  cases s <;> simp only [SquareSymmetry.act, Cell.add] at a b c d <;> omega

end LeanTrominoes.PlusRefinement

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The reserved top-left corner contains a solid 2-by-2 square. -/
theorem unitSquare_subset_tile {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) : PlusRefinement.unitSquare ⊆ tile n holes := by
  intro c hc
  apply lower_tile hn holes admissible
  simp only [PlusRefinement.unitSquare, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
      KeyCornerArithmetic.inKey] <;> omega

/-- Every rigid placement of Q has a cell outside any cross-refined region. -/
theorem tile_not_inside_refinement {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (original : Set Cell) (p : Placement Unit) :
    ¬ ∀ c ∈ p.cells (fun _ => tile n holes), c ∈ PlusRefinement.region original := by
  intro inside
  apply PlusRefinement.no_oriented_unitSquare original p.symmetry p.offset
  intro c hc
  exact inside _ ((Placement.mem_cells_iff _ _ _).mpr
    ⟨c, unitSquare_subset_tile hn holes admissible hc, rfl⟩)

end LeanTrominoes.KeyedPeriodicComplement
