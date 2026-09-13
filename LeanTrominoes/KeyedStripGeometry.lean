/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripGridCompactness
import LeanTrominoes.KeyedStripGridRecovery

/-! # Exact simulation by two tiles in a full bounded strip -/

namespace LeanTrominoes.KeyedStripComplement
open KeyedPeriodicComplement (AdmissibleHoles)

theorem pair_tileable_iff {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = PlusRefinement.region original) :
    Tileable (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ↔
      Tromino.I.Tileable original := by
  constructor
  · intro tiled
    obtain ⟨ps,ht,seed⟩ := normalize hn holes admissible tiled
    obtain ⟨qs,hq,grid⟩ := exists_tiling_with_grid hn period holes admissible ps ht seed
    exact recover_tromino_of_grid hn holes admissible original carrier qs hq grid
  · intro tiled
    have small := (PlusRefinement.bumpy_tileable_refinement_iff original).mpr tiled
    have subset : PlusRefinement.region original ⊆ horizontalStrip n := by
      rw [← carrier]
      exact fun _ h => h.1
    apply tileable_pair_of_difference _ _ _ _ subset small
    rw [← carrier]
    exact ⟨_,grid_tiling (by omega) holes⟩

end LeanTrominoes.KeyedStripComplement
