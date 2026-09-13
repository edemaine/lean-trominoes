/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripRefinedExclusion
import LeanTrominoes.BumpyTrominoRefinement
import LeanTrominoes.TilingPairRegion

/-! # Recovering a tromino tiling from a complete background grid -/

namespace LeanTrominoes.KeyedStripComplement
open KeyedPeriodicComplement (AdmissibleHoles)

/-- Once every canonical Q is present, no additional Q can occur in the
refined holes. Consequently the remaining P tiles contract to a tromino tiling. -/
theorem recover_tromino_of_grid {n : Nat} (hn : 96 ≤ n)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region original)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps)
    (grid : ∀ p ∈ gridPlacements n, p.tag true ∈ ps) : Tromino.I.Tileable original := by
  have subset : PlusRefinement.region original ⊆ horizontalStrip n := by
    rw [← carrier]
    exact fun _ h => h.1
  have canonical := grid_tiling (by omega : 0 < n) holes
  have exact_grid : {p : Placement Unit | p.tag true ∈ ps} = gridPlacements n := by
    apply Set.Subset.antisymm
    · intro p hp
      by_contra absent
      apply tile_not_inside_refinement hn holes admissible original p
      intro c hc
      rw [← carrier]
      by_contra outside
      obtain ⟨q, hq, hqc⟩ := canonical.exists_cover ⟨tiling.tilesInside (p.tag true) hp c hc,outside⟩
      have different : p.tag true ≠ q.tag true := by
        intro eq
        have equal := congrArg Placement.untag eq
        simp only [Placement.untag_tag] at equal
        exact absent (equal ▸ hq)
      have disjoint := tiling.disjoint_cells hp (grid q hq) different
      exact (Finset.disjoint_left.mp disjoint) hc hqc
    · exact grid
  have background : IsTiling (fun _ : Unit => tile n holes)
      (horizontalStrip n \ PlusRefinement.region original) {p | p.tag true ∈ ps} := by
    rw [exact_grid, ← carrier]
    exact canonical
  exact (PlusRefinement.bumpy_tileable_refinement_iff original).mp
    (tileable_left_of_region_background _ _ _ _ subset ps tiling background)

end LeanTrominoes.KeyedStripComplement
