/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementPropagation
import LeanTrominoes.TilingPrescribedCompactness
import Mathlib.Tactic.Ring

/-! # A mixed tiling containing the complete canonical Q grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

private def gridPatch (n r : Nat) : Set (Placement Bool) :=
  {p | ∃ i j : Int, -(r : Int) ≤ i ∧ i ≤ r ∧ -(r : Int) ≤ j ∧ j ≤ r ∧
    p = ⟨true, .identity, ((n : Int) * i, (n : Int) * j)⟩}

/-- Compactness converts the forced quadrant into a new mixed tiling with
every canonical Q placement present. -/
theorem exists_tiling_with_grid {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ placements)
    (seed : referencePlacement ∈ placements) :
    ∃ ps, IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ ps ∧
      ∀ p ∈ gridPlacements n, p.tag true ∈ ps := by
  have increasing : ∀ r, gridPatch n r ⊆ gridPatch n (r + 1) := by
    rintro r p ⟨i, j, hi₀, hi₁, hj₀, hj₁, hp⟩
    exact ⟨i, j, by omega, by omega, by omega, by omega, hp⟩
  have realized : ∀ r, ∃ ps,
      IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ ps ∧
        gridPatch n r ⊆ ps := by
    intro r
    let offset : Cell := ((n : Int) * r, -(n : Int) * r)
    refine ⟨{p | p.shift offset ∈ placements}, tiling.recenter offset, ?_⟩
    rintro p ⟨i, j, hi₀, hi₁, hj₀, hj₁, rfl⟩
    have hi : (((r : Int) + i).toNat : Int) = (r : Int) + i := by omega
    have hj : (((r : Int) - j).toNat : Int) = (r : Int) - j := by omega
    have forced := quadrant_placements hn period holes admissible placements tiling
      (0, 0) seed ((r : Int) + i).toNat ((r : Int) - j).toNat
    have eq : (⟨true, .identity, ((n : Int) * i, (n : Int) * j)⟩ : Placement Bool).shift offset =
        ⟨true, .identity,
          Cell.add (0, 0) ((n : Int) * ((r : Int) + i).toNat,
            -(n : Int) * ((r : Int) - j).toNat)⟩ := by
      apply Placement.ext
      · rfl
      · rfl
      · apply Prod.ext <;> dsimp [Placement.shift, offset, Cell.add] <;>
          simp only [hi, hj] <;> ring
    change _ ∈ placements
    rwa [eq]
  obtain ⟨ps, ht, patches⟩ := TilingSelection.exists_tiling_of_prescriptions
    (pairTiles PlusRefinement.bumpy (tile n holes)) (gridPatch n) increasing realized
  refine ⟨ps, ht, ?_⟩
  rintro p ⟨hs, i, j, hp⟩
  apply patches (max i.natAbs j.natAbs)
  refine ⟨i, j, ?_, ?_, ?_, ?_, ?_⟩
  · have : -(i.natAbs : Int) ≤ i := by simpa [Int.natCast_natAbs] using neg_abs_le i
    have := Nat.le_max_left i.natAbs j.natAbs
    omega
  · have : i ≤ (i.natAbs : Int) := Int.le_natAbs
    have := Nat.le_max_left i.natAbs j.natAbs
    omega
  · have : -(j.natAbs : Int) ≤ j := by simpa [Int.natCast_natAbs] using neg_abs_le j
    have := Nat.le_max_right i.natAbs j.natAbs
    omega
  · have : j ≤ (j.natAbs : Int) := Int.le_natAbs
    have := Nat.le_max_right i.natAbs j.natAbs
    omega
  · exact Placement.ext rfl hs hp

end LeanTrominoes.KeyedPeriodicComplement
