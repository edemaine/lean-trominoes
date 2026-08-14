/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationLiftLookup
import LeanTrominoes.PeriodicThreeDMNormalizationStripPositionGeometry

/-!
# Period translations for normalized 3DM strip provenance
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Translate between copies of a rectangular strip fundamental domain. -/
def PlanarPresentation.stripPeriodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (translate : Cell) : Cell :=
  ((presentation.finalNormalizationPeriod : Int) * translate.1,
    (presentation.finalStripHeight : Int) * translate.2)

/-- The canonical finite representative is coordinatewise Euclidean
remainder modulo the strip width and height. -/
theorem PlanarPresentation.stripFiniteLocation_eq_mod
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (location : Cell) :
    presentation.stripFiniteLocation location =
      (location.1 % presentation.finalNormalizationPeriod,
        location.2 % presentation.finalStripHeight) := by
  simp only [PlanarPresentation.stripFiniteLocation,
    PeriodicOrthogonalDrawing.positionAt]
  apply Prod.ext
  · change
      ((PeriodicOrthogonalDrawing.residue location.1
        presentation.stripNormalizedOrthogonalDrawing.horizontalPeriodPred).val :
          Int) = location.1 % presentation.finalNormalizationPeriod
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.stripNormalizedOrthogonalDrawing.horizontalPeriodPred : Int) +
            1 = (presentation.finalNormalizationPeriod : Int) := by
      exact_mod_cast presentation.stripNormalizedOrthogonalDrawing_periods.1
    rw [periodEquality]
  · change
      ((PeriodicOrthogonalDrawing.residue location.2
        presentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred).val :
          Int) = location.2 % presentation.finalStripHeight
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred : Int) +
            1 = (presentation.finalStripHeight : Int) := by
      exact_mod_cast presentation.stripNormalizedOrthogonalDrawing_periods.2
    rw [periodEquality]

/-- Equality with the finite key of an in-range geometric point reconstructs
an explicit rectangular strip-period translate. -/
theorem PlanarPresentation.exists_stripPeriodTranslation_of_finite_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (location point : Cell)
    (verticalBounds :
      0 ≤ (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 ∧
      (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 <
        (presentation.finalStripHeight : Int))
    (equal : presentation.stripFiniteLocation location =
      stripRasterLocation presentation.finalNormalizationPeriod point) :
    ∃ translate : Cell,
      location = Cell.add
        (stripReflectedLocation presentation.finalNormalizationPeriod point)
        (presentation.stripPeriodTranslation translate) := by
  rw [presentation.stripFiniteLocation_eq_mod] at equal
  rcases location with ⟨locationX, locationY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [stripRasterLocation, stripReflectedLocation,
    Prod.mk.injEq] at equal verticalBounds ⊢
  have horizontalMod :
      locationX ≡ pointX
        [ZMOD (presentation.finalNormalizationPeriod : Int)] := equal.1
  have verticalMod :
      locationY ≡
        2 * (presentation.finalNormalizationPeriod : Int) - pointY
        [ZMOD (presentation.finalStripHeight : Int)] := by
    change locationY % (presentation.finalStripHeight : Int) =
      (2 * (presentation.finalNormalizationPeriod : Int) - pointY) %
        presentation.finalStripHeight
    rw [Int.emod_eq_of_lt verticalBounds.1 verticalBounds.2]
    exact equal.2
  rcases Int.modEq_iff_add_fac.mp horizontalMod with
    ⟨horizontalTranslate, horizontalEqual⟩
  rcases Int.modEq_iff_add_fac.mp verticalMod with
    ⟨verticalTranslate, verticalEqual⟩
  refine ⟨(-horizontalTranslate, -verticalTranslate), ?_⟩
  simp only [Cell.add, PlanarPresentation.stripPeriodTranslation,
    Prod.mk.injEq]
  constructor <;> nlinarith

/-- Adding an explicit rectangular period translation to an in-range
geometric point recovers its finite strip key. -/
theorem PlanarPresentation.stripFiniteLocation_add_stripPeriodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (point translate : Cell)
    (verticalBounds :
      0 ≤ (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 ∧
      (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 <
        (presentation.finalStripHeight : Int)) :
    presentation.stripFiniteLocation
        (Cell.add
          (stripReflectedLocation presentation.finalNormalizationPeriod point)
          (presentation.stripPeriodTranslation translate)) =
      stripRasterLocation presentation.finalNormalizationPeriod point := by
  rw [presentation.stripFiniteLocation_eq_mod]
  rcases point with ⟨pointX, pointY⟩
  rcases translate with ⟨translateX, translateY⟩
  simp only [stripReflectedLocation, stripRasterLocation, Cell.add,
    PlanarPresentation.stripPeriodTranslation,
    Prod.mk.injEq] at verticalBounds ⊢
  constructor
  · simp [Int.add_emod]
  · have baseMod :
        (2 * (presentation.finalNormalizationPeriod : Int) - pointY) %
            presentation.finalStripHeight =
          2 * (presentation.finalNormalizationPeriod : Int) - pointY :=
      Int.emod_eq_of_lt verticalBounds.1 verticalBounds.2
    rw [Int.add_emod]
    simp [baseMod]

/-- Positive strip dimensions make rectangular period translations
injective. -/
theorem PlanarPresentation.stripPeriodTranslation_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    Function.Injective presentation.stripPeriodTranslation := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [PlanarPresentation.stripPeriodTranslation,
    Prod.mk.injEq] at equal ⊢
  have widthNonzero : (presentation.finalNormalizationPeriod : Int) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt presentation.finalNormalizationPeriod_pos
  have heightPositive : 0 < presentation.finalStripHeight := by
    unfold PlanarPresentation.finalStripHeight
    omega
  have heightNonzero : (presentation.finalStripHeight : Int) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt heightPositive
  constructor
  · exact mul_left_cancel₀ widthNonzero equal.1
  · exact mul_left_cancel₀ heightNonzero equal.2

end PeriodicThreeDM
end LeanTrominoes
