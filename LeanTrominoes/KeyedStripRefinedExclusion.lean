/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripOrientation
import LeanTrominoes.KeyedComplementRefinedExclusion

/-! # Excluding additional strip backgrounds from the refined source -/

namespace LeanTrominoes.KeyedStripComplement
open KeyedPeriodicComplement (AdmissibleHoles)

/-- The reserved top-left corner contains a solid 2-by-2 square. -/
theorem unitSquare_subset_tile {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) : PlusRefinement.unitSquare ⊆ tile n holes := by
  intro c hc
  apply lower_tile hn holes admissible
  simp only [PlusRefinement.unitSquare, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inHorizontalLock,
      inKey] <;> omega

/-- Every rigid placement of Q has a cell outside any cross-refined region. -/
theorem tile_not_inside_refinement {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (original : Set Cell) (p : Placement Unit) :
    ¬ ∀ c ∈ p.cells (fun _ => tile n holes), c ∈ PlusRefinement.region original := by
  intro inside
  apply PlusRefinement.no_oriented_unitSquare original p.symmetry p.offset
  intro c hc
  exact inside _ ((Placement.mem_cells_iff _ _ _).mpr
    ⟨c, unitSquare_subset_tile hn holes admissible hc, rfl⟩)

end LeanTrominoes.KeyedStripComplement
