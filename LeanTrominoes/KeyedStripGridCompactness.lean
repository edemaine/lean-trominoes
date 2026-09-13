/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripPropagation
import LeanTrominoes.TilingRegionPrescribedCompactness
import Mathlib.Tactic.Ring

/-! # A mixed tiling containing the complete canonical Q row -/

namespace LeanTrominoes.KeyedStripComplement

open KeyedPeriodicComplement (AdmissibleHoles referencePlacement)

private def gridPatch (n r : Nat) : Set (Placement Bool) :=
  {p | ∃ i : Int, -(r : Int) ≤ i ∧ i ≤ r ∧
    p = ⟨true, .identity, ((n : Int) * i, 0)⟩}

/-- Compactness converts the forced ray into a new mixed tiling with
every canonical Q placement present. -/
theorem exists_tiling_with_grid {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) placements)
    (seed : referencePlacement ∈ placements) :
    ∃ ps, IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps ∧
      ∀ p ∈ gridPlacements n, p.tag true ∈ ps := by
  have increasing : ∀ r, gridPatch n r ⊆ gridPatch n (r + 1) := by
    rintro r p ⟨i, hi₀, hi₁, hp⟩
    exact ⟨i, by omega, by omega, hp⟩
  have realized : ∀ r, ∃ ps,
      IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) ps ∧
        gridPatch n r ⊆ ps := by
    intro r
    let offset : Cell := ((n : Int) * r, 0)
    refine ⟨{p | p.shift offset ∈ placements}, recenter_horizontal tiling ((n : Int)*r), ?_⟩
    rintro p ⟨i, hi₀, hi₁, rfl⟩
    have hi : (((r : Int) + i).toNat : Int) = (r : Int) + i := by omega
    have forced := ray_placements hn period holes admissible placements tiling
      seed ((r : Int) + i).toNat
    have eq : (⟨true, .identity, ((n : Int) * i, 0)⟩ : Placement Bool).shift offset =
        ⟨true, .identity,
          ((n : Int) * ((r : Int) + i).toNat, 0)⟩ := by
      apply Placement.ext
      · rfl
      · rfl
      · apply Prod.ext <;> dsimp [Placement.shift, offset, Cell.add] <;>
          simp only [hi] <;> ring
    change _ ∈ placements
    rwa [eq]
  obtain ⟨ps, ht, patches⟩ := RegionTilingSelection.exists_tiling_of_prescriptions
    (pairTiles PlusRefinement.bumpy (tile n holes)) (horizontalStrip n) (gridPatch n) increasing realized
  refine ⟨ps, ht, ?_⟩
  rintro p ⟨hs, i, hp⟩
  apply patches i.natAbs
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa [Int.natCast_natAbs] using neg_abs_le i
  · exact Int.le_natAbs
  · exact Placement.ext rfl hs hp

end LeanTrominoes.KeyedStripComplement
