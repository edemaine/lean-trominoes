/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMSourceBlankRegion
import LeanTrominoes.PeriodicTrominoPadding
import LeanTrominoes.TilingRegionTranslation
import LeanTrominoes.KeyedComplementDisconnected

/-! # Centering and padding the concrete hard source for Theorem 5.5 -/

namespace LeanTrominoes.Theorem55Source

open PeriodicThreeDM

variable {problem : PeriodicThreeDM}

def period (presentation : problem.PlanarPresentation) : Nat :=
  6 * presentation.finalNormalizationPeriod

def shifted (presentation : problem.PlanarPresentation) : Set Cell :=
  {c | Cell.add (54, 18) c ∈
    (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier}

/-- The centered hard source, augmented by a separated tileable rectangle. -/
def region (presentation : problem.PlanarPresentation) : Set Cell :=
  shifted presentation ∪ PeriodicTrominoPadding.region (period presentation)

theorem period_large (presentation : problem.PlanarPresentation) : 72 ≤ period presentation := by
  simp [period, PlanarPresentation.finalNormalizationPeriod,
    vertexNormalizationScaleNat, PeriodicGridDrawing.gridSize]
  omega

theorem seventyTwo_dvd_period (presentation : problem.PlanarPresentation) :
    (72 : Int) ∣ (period presentation : Int) := by
  obtain ⟨k, hk⟩ := presentation.twelve_dvd_finalNormalizationPeriod
  refine ⟨k, ?_⟩
  simp only [period, Nat.cast_mul, Nat.cast_ofNat, hk]
  ring

theorem padding_disjoint (presentation : problem.PlanarPresentation) :
    Disjoint (shifted presentation) (PeriodicTrominoPadding.region (period presentation)) := by
  apply Set.disjoint_left.mpr
  intro c hs hp
  have residues := PeriodicTrominoPadding.residues_mod_seventyTwo
    (seventyTwo_dvd_period presentation) c hp
  apply presentation.periodicRegion_blank_of_residues .I (Cell.add (54, 18) c) ?_ ?_ ?_ hs
  all_goals dsimp [Cell.add]; omega

theorem padding_separated (presentation : problem.PlanarPresentation) :
    ∀ a ∈ shifted presentation,
      ∀ b ∈ PeriodicTrominoPadding.region (period presentation), ¬ Cell.SideAdjacent a b := by
  intro a ha b hb adjacent
  have residues := PeriodicTrominoPadding.residues_mod_seventyTwo
    (seventyTwo_dvd_period presentation) b hb
  apply presentation.periodicRegion_blank_of_residues .I (Cell.add (54, 18) a) ?_ ?_ ?_ ha
  all_goals
    dsimp [Cell.add]
    unfold Cell.SideAdjacent at adjacent
    omega

/-- Centering and padding preserve the hard source's tileability exactly. -/
theorem tileable_iff (presentation : problem.PlanarPresentation) :
    Tromino.I.Tileable (region presentation) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  rw [region, i_tileable_union_iff _ _ (padding_disjoint presentation)
    (padding_separated presentation) (PeriodicTrominoPadding.tileable (period_large presentation))]
  exact tileable_recenter_region_iff _ _ (54, 18)

/-- The padding supplies the 2-by-2 source block used to disconnect Q. -/
theorem source_square (presentation : problem.PlanarPresentation) :
    ∀ c ∈ PlusRefinement.unitSquare, Cell.add (14, 4) c ∈ region presentation := by
  intro c hc
  right
  apply PeriodicTrominoPadding.mem_of_coordinates (period_large presentation)
  all_goals
    simp only [PlusRefinement.unitSquare, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> decide

private theorem corner_residue (n x : Int) (hn : 0 < n) (divisor : (72 : Int) ∣ n)
    (corner : x % n ≤ 6 ∨ n - 6 ≤ x % n) : x % 72 ≤ 6 ∨ 66 ≤ x % 72 := by
  have nonnegative := Int.emod_nonneg x (by omega : n ≠ 0)
  have below := Int.emod_lt_of_pos x hn
  have periodMod := Int.emod_eq_zero_of_dvd divisor
  rw [← Int.emod_emod_of_dvd x divisor]
  omega

/-- The source remains empty in all corner neighborhoods after padding. -/
theorem blank_corners (presentation : problem.PlanarPresentation) (c : Cell)
    (hx : c.1 % (period presentation : Int) ≤ 6 ∨
      (period presentation : Int) - 6 ≤ c.1 % (period presentation : Int))
    (hy : c.2 % (period presentation : Int) ≤ 6 ∨
      (period presentation : Int) - 6 ≤ c.2 % (period presentation : Int)) :
    c ∉ region presentation := by
  have hn : (0 : Int) < period presentation := by have := period_large presentation; omega
  have cx := corner_residue _ c.1 hn (seventyTwo_dvd_period presentation) hx
  have cy := corner_residue _ c.2 hn (seventyTwo_dvd_period presentation) hy
  rintro (source | padding)
  · apply presentation.periodicRegion_blank_of_residues .I (Cell.add (54, 18) c) ?_ ?_ ?_ source
    all_goals dsimp [Cell.add]; omega
  · have residues := PeriodicTrominoPadding.residues_mod_seventyTwo
      (seventyTwo_dvd_period presentation) c padding
    omega

end LeanTrominoes.Theorem55Source
