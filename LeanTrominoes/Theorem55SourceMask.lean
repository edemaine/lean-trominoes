/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55SourcePeriodicity
import LeanTrominoes.SquarePeriodicMask
import LeanTrominoes.Theorem55Geometry

/-! # The finite hole mask for the concrete hard source -/

namespace LeanTrominoes.Theorem55Source

open KeyedPeriodicComplement

variable {problem : PeriodicThreeDM}

noncomputable def holes (presentation : problem.PlanarPresentation) : Polyomino :=
  mask (3 * period presentation) (PlusRefinement.region (region presentation))

theorem holes_carrier (presentation : problem.PlanarPresentation) :
    holesRegion (3 * period presentation) (holes presentation) =
      PlusRefinement.region (region presentation) := by
  apply holesRegion_mask
  · have := period_large presentation
    omega
  · exact PlusRefinement.isSquarePeriodic (isSquarePeriodic presentation)

private theorem parent_corner (n parent subcell : Int)
    (lo : -1 ≤ subcell) (hi : subcell ≤ 1)
    (box : 0 ≤ 3 * parent + subcell ∧ 3 * parent + subcell < 3 * n)
    (corner : 3 * parent + subcell < 18 ∨ 3 * n - 18 ≤ 3 * parent + subcell) :
    parent % n ≤ 6 ∨ n - 6 ≤ parent % n := by
  have bounds : 0 ≤ parent ∧ parent ≤ n := by omega
  by_cases equal : parent = n
  · simp [equal]
  · have below : parent < n := by omega
    rw [Int.emod_eq_of_lt bounds.1 below]
    omega

theorem refined_mask_admissible (n : Nat) (original : Set Cell)
    (blank : ∀ c : Cell, (c.1 % (n : Int) ≤ 6 ∨ (n : Int) - 6 ≤ c.1 % (n : Int)) →
      (c.2 % (n : Int) ≤ 6 ∨ (n : Int) - 6 ≤ c.2 % (n : Int)) → c ∉ original) :
    AdmissibleHoles (3 * n) (mask (3 * n) (PlusRefinement.region original)) := by
  intro c hc
  rw [mem_mask] at hc
  obtain ⟨box, member⟩ := hc
  refine ⟨PlusRefinement.region_mod_three member, ?_⟩
  intro corner
  obtain ⟨parent, hp, subcell, hu, rfl⟩ := member
  have bounds : -1 ≤ subcell.1 ∧ subcell.1 ≤ 1 ∧ -1 ≤ subcell.2 ∧ subcell.2 ≤ 1 := by
    simp only [PlusRefinement.cross, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [mem_square] at box
  simp only [PlusRefinement.pixel, Cell.add, Cell.scale, Nat.cast_mul,
    Nat.cast_ofNat] at box corner
  exact blank parent
    (parent_corner _ _ _ bounds.1 bounds.2.1 ⟨box.1, box.2.1⟩ corner.1)
    (parent_corner _ _ _ bounds.2.2.1 bounds.2.2.2 ⟨box.2.2.1, box.2.2.2⟩ corner.2) hp

theorem holes_admissible (presentation : problem.PlanarPresentation) :
    AdmissibleHoles (3 * period presentation) (holes presentation) :=
  refined_mask_admissible _ _ (blank_corners presentation)

/-- The geometric construction applies to every prepared hard-source presentation. -/
theorem planeProblem_iff (presentation : problem.PlanarPresentation) (input : List Cell)
    (encoding : input.toFinset = tile (3 * period presentation) (holes presentation)) :
    Theorem55.planeProblem input ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  have large := period_large presentation
  have eq := Theorem55.planeProblem_iff_of_source_square (n := 3 * period presentation)
    (by omega) (by omega) (holes presentation) (holes_admissible presentation)
    (region presentation) (holes_carrier presentation) (14, 4)
    (by decide) (by decide) (by dsimp; omega) (by dsimp; omega)
    (source_square presentation) input encoding
  exact eq.trans (tileable_iff presentation)

end LeanTrominoes.Theorem55Source
