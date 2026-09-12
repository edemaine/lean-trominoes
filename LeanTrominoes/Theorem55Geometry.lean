/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55Construction
import LeanTrominoes.KeyedComplementGridCompactness
import LeanTrominoes.KeyedComplementGridRecovery

/-! # Exact tileability equivalence for the two-polyomino construction

The geometric reduction is valid for masks on the cross grid with reserved
corner margins. `Theorem55SourceMask` establishes these promises and
disconnectedness for the concrete hard-source family; `Theorem55Proof`
supplies the completed plane co-r.e.-completeness theorem.
-/

namespace LeanTrominoes.Theorem55

/-- The explicit pair tiles the plane exactly when the source region is
I-tromino tileable, provided the mask has the stated geometric promises.
All placements may rotate or reflect. -/
theorem pair_tileable_iff {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (original : Set Cell)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = PlusRefinement.region original) :
    Tileable (pairTiles PlusRefinement.bumpy (KeyedPeriodicComplement.tile n holes)) Set.univ ↔
      Tromino.I.Tileable original := by
  constructor
  · intro h
    obtain ⟨ps, ht, seed⟩ := tileable_pair_normalize _ _
      PlusRefinement.bumpy_not_tileable_plane h
    obtain ⟨qs, qt, grid⟩ := KeyedPeriodicComplement.exists_tiling_with_grid
      hn period holes admissible ps ht seed
    exact KeyedPeriodicComplement.recover_tromino_of_grid hn holes admissible original carrier qs qt grid
  · exact pair_tileable_of_tromino (by omega) holes original carrier

/-- With a source 2-by-2 block certifying disconnectedness, the construction
has exactly the intended target predicate, including its connectivity check. -/
theorem planeProblem_iff_of_source_square {n : Nat} (hn : 96 ≤ n)
    (period : (n : Int) % 3 = 0) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (original : Set Cell)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = PlusRefinement.region original)
    (parent : Cell) (hx : 4 ≤ 3 * parent.1) (hy : 4 ≤ 3 * parent.2)
    (hx' : 3 * parent.1 + 3 < n) (hy' : 3 * parent.2 + 3 < n)
    (block : ∀ c ∈ PlusRefinement.unitSquare, Cell.add parent c ∈ original)
    (input : List Cell) (encoding : input.toFinset = KeyedPeriodicComplement.tile n holes) :
    planeProblem input ↔ Tromino.I.Tileable original := by
  have nonempty := KeyedPeriodicComplement.tile_nonempty hn holes admissible
  have disconnected := KeyedPeriodicComplement.tile_disconnected_of_source_square hn holes
    admissible original carrier parent hx hy hx' hy' block
  simp only [planeProblem, encoding, nonempty, disconnected, not_false_eq_true, true_and]
  exact pair_tileable_iff hn period holes admissible original carrier

end LeanTrominoes.Theorem55
