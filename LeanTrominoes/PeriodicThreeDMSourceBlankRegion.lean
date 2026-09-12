/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMNormalizationBlankMargin
import LeanTrominoes.GadgetBehavior

/-! # Blank rectangles in the actual periodic tromino source -/

namespace LeanTrominoes.PeriodicThreeDM

open Gadget

private theorem paper_pixel_bounds (tromino : Tromino) (cellType : OrthogonalCellType) :
    ∀ c ∈ orthogonalCellPixels tromino cellType,
      0 ≤ c.1 ∧ c.1 < 6 ∧ 0 ≤ c.2 ∧ c.2 < 6 := by
  cases tromino <;> cases cellType with
  | blank => decide +kernel
  | wire axis color => cases axis <;> cases color <;> decide +kernel
  | bend bend color => cases bend <;> cases color <;> decide +kernel
  | monochromaticVertex color => cases color <;> decide +kernel
  | trichromaticVertex order => cases order <;> decide +kernel

/-- Every normalized source has the same empty 30-by-30 residue rectangle
after substituting the six-by-six tromino gadgets. -/
theorem PlanarPresentation.periodicRegion_blank_of_residues
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation)
    (tromino : Tromino) (c : Cell)
    (hx : 42 ≤ c.1 % 72) (hy : 6 ≤ c.2 % 72) (hy' : c.2 % 72 < 36) :
    c ∉ (presentation.normalizedOrthogonalDrawing.periodicRegion tromino).carrier := by
  obtain ⟨location, window⟩ := latticeBlockWindows_cover c
  obtain ⟨pixel, pixelMember, eq⟩ := Finset.mem_image.mp window
  have bounds := (mem_rectangleCells_iff 6 6 pixel).mp pixelMember
  have ex := congrArg Prod.fst eq
  have ey := congrArg Prod.snd eq
  dsimp [latticeBlockOrigin, Cell.add] at ex ey
  have blank := presentation.normalizedOrthogonalDrawing_getAt_blank_of_residues location
    (by omega) (by omega) (by omega)
  intro member
  rw [PeriodicOrthogonalDrawing.periodicRegion_carrier_eq,
    ← liftedGadgetCarrier_eq_expandedCarrier] at member
  obtain ⟨other, localMember⟩ := member
  obtain ⟨q, hq, qe⟩ := Finset.mem_image.mp localMember
  have paper : q ∈ orthogonalCellPixels tromino
      (presentation.normalizedOrthogonalDrawing.getAt other) := List.mem_toFinset.mp hq
  have rectangle : q ∈ rectangleCells 6 6 :=
    (mem_rectangleCells_iff 6 6 q).mpr (paper_pixel_bounds tromino _ q paper)
  have otherWindow : c ∈ latticeBlockWindow other := Finset.mem_image.mpr ⟨q, rectangle, qe⟩
  have same := latticeBlockWindow_unique otherWindow window
  subst other
  simp [blank, orthogonalCellPixels] at paper

/-- Centering the period at `(54,18)` leaves room both for the corner keys
and for an isolated tileable padding rectangle. -/
theorem PlanarPresentation.periodicRegion_blank_near_origin
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation)
    (tromino : Tromino) (c : Cell)
    (hx : -12 ≤ c.1) (hx' : c.1 < 18) (hy : -12 ≤ c.2) (hy' : c.2 < 18) :
    Cell.add (54, 18) c ∉
      (presentation.normalizedOrthogonalDrawing.periodicRegion tromino).carrier := by
  apply presentation.periodicRegion_blank_of_residues
  all_goals dsimp [Cell.add]; omega

end LeanTrominoes.PeriodicThreeDM
