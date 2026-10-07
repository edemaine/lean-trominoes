/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPolyominoSeedQuarterSoundness
import LeanTrominoes.Theorem55SourceMask
import LeanTrominoes.FinitePolyominoCompletionCoRE
import LeanTrominoes.BumpyTrominoConnected

/-! # The two fixed polyominoes for finite-seed completion -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed
open PlusRefinement Gadget KeyedPeriodicComplement

abbrev presentation := FixedPlanarThreeDMSeed.fixedPresentation.toPlanarPresentation
abbrev drawing := FixedNormalizedOrientationSeed.fixedDrawing
def coarsePeriod : Nat := Theorem55Source.period presentation
attribute [local irreducible] coarsePeriod
def tilePeriod : Nat := 3 * coarsePeriod
def fixedHoles : Polyomino := mask tilePeriod (region (ShiftedGadgetReadout.original drawing (9,3)))
def smallTile : Polyomino := bumpy
def largeTile : Polyomino := tile tilePeriod fixedHoles
def Problem := FinitePolyominoCompletion.fixedProblem smallTile.toList largeTile.toList

theorem coarsePeriod_large : 72 ≤ coarsePeriod := by
  unfold coarsePeriod
  exact Theorem55Source.period_large presentation
theorem tilePeriod_large : 96 ≤ tilePeriod := by unfold tilePeriod; have := coarsePeriod_large; omega
theorem tilePeriod_divisible : (tilePeriod : Int) % 3 = 0 := by
  change ((3 : Int)*(coarsePeriod : Int)) % 3 = 0
  omega

theorem original_eq_shifted : ShiftedGadgetReadout.original drawing (9,3) = Theorem55Source.shifted presentation := rfl

theorem original_periodic : IsSquarePeriodic coarsePeriod (ShiftedGadgetReadout.original drawing (9,3)) := by
  rw [original_eq_shifted]
  apply IsSquarePeriodic.recenter
  apply PeriodicRegion.isSquarePeriodic
  · simp only [PeriodicOrthogonalDrawing.periodicRegion,PeriodicOrthogonalDrawing.horizontalPeriod,
      presentation.normalizedOrthogonalDrawing_periods.1,coarsePeriod,Theorem55Source.period,Nat.cast_mul,Nat.cast_ofNat]
  · simp only [PeriodicOrthogonalDrawing.periodicRegion,PeriodicOrthogonalDrawing.verticalPeriod,
      presentation.normalizedOrthogonalDrawing_periods.2,coarsePeriod,Theorem55Source.period,Nat.cast_mul,Nat.cast_ofNat]

theorem fixedHoles_carrier : holesRegion tilePeriod fixedHoles =
    region (ShiftedGadgetReadout.original drawing (9,3)) :=
  holesRegion_mask (by have := tilePeriod_large; omega) _ (PlusRefinement.isSquarePeriodic original_periodic)

theorem fixedHoles_admissible : AdmissibleHoles tilePeriod fixedHoles := by
  change AdmissibleHoles (3 * coarsePeriod)
    (mask (3 * coarsePeriod) (region (ShiftedGadgetReadout.original drawing (9,3))))
  apply Theorem55Source.refined_mask_admissible coarsePeriod
    (ShiftedGadgetReadout.original drawing (9,3))
  intro c hx hy member
  unfold coarsePeriod at hx hy
  apply Theorem55Source.blank_corners presentation c hx hy
  exact Or.inl (original_eq_shifted ▸ member)

theorem smallTile_properties : smallTile.card = 15 ∧ Polyomino.IsConnected smallTile :=
  ⟨bumpy_card,bumpy_connected⟩

theorem largeTile_nonempty : largeTile.Nonempty :=
  tile_nonempty tilePeriod_large fixedHoles fixedHoles_admissible

theorem coRE : LeanWang.CoREPred Problem := FinitePolyominoCompletion.fixedProblem_coRE _ _

end LeanTrominoes.FixedPolyominoSeed
