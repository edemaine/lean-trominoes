/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FixedRetainedExactOneSeedCompleteness
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedPolaritySeed
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarThreeDMTotalSeedReduction

/-! # Co-r.e.-complete finite prescriptions in one fixed planar periodic 3DM instance -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPlanarThreeDMSeed
open LeanWang PeriodicOrthocrossing PeriodicCNF.SignedDecoder

abbrev SourceVariable := FixedThreeSATThreeSeed.Variable
abbrev FinalVariable := RetainedOrderedFixedEightOneInThreeVariable SourceVariable
abbrev Variable := PolarityNormalizedVariable FinalVariable
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq Variable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
local instance : BEq FinalVariable := instBEqOfDecidableEq
local instance : LawfulBEq FinalVariable := by infer_instance
local instance : BEq Variable := instBEqOfDecidableEq
local instance : LawfulBEq Variable := by infer_instance

abbrev source := FixedThreeSATThreeSeed.fixedFormula
def fixedFormula : PeriodicCNF Variable :=
  (retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed source).anchorNormalize
def fixedInstance : PeriodicThreeDM := PeriodicPlanarOneInThreeToThreeDM.encodedProblem fixedFormula
def Problem := Prescribed fixedInstance.Satisfies

theorem source_occurrences :
    @PeriodicCNF.OccurrencesAtMost SourceVariable instBEqOfDecidableEq (by infer_instance) 3 source :=
  PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 source
    FixedThreeSATThreeSeed.fixedFormula_occurrencesAtMostThree

private theorem final_occurrences :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase.OccurrencesAtMost 3 := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
    (PeriodicPlanarSAT.ExactOneEndpoint.occurrences source FixedThreeSATThreeSeed.fixedFormula_isLocal
      FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
      FixedThreeSATThreeSeed.fixedFormula_clausesNonempty)

theorem fixedFormula_occurrences : fixedFormula.OccurrencesAtMost 3 := by
  have normalized := PeriodicOneInThreePolarityNormalization.formula_occurrencesAtMostThree
    _ ((PeriodicCNF.anchorNormalize_occurrencesAtMost _ 3) final_occurrences)
  have normalized' : @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3
      (PeriodicOneInThreePolarityNormalization.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase.anchorNormalize) :=
    PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _ normalized
  have gauged := normalized'.variableGauge
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge
  exact PeriodicCNF.anchorNormalize_occurrencesAtMost _ 3
    (PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _ gauged)

private theorem final_arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase := by
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
    source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty]
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
    source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem fixedFormula_arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree fixedFormula :=
  PeriodicCNF.anchorNormalize_arityTwoOrThree _
    ((PeriodicOneInThreePolarityNormalization.formula_arityTwoOrThree
      (PeriodicCNF.anchorNormalize_arityTwoOrThree _ final_arity)).variableGauge
        PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge)

def reduction (seed : PeriodicCNF.Seed SourceVariable) : PeriodicCNF.Seed Nat :=
  PeriodicPlanarOneInThreeToThreeDM.totalSeedReduction fixedFormula
    (transportSeed (retainedPolaritySeedRead source) seed)

theorem reduction_primrec : Primrec reduction :=
  (PeriodicPlanarOneInThreeToThreeDM.totalSeedReduction_primrec fixedFormula).comp
    (transportSeed_primrec (retainedPolaritySeedRead_primrec source))

theorem reduction_correct (seed : PeriodicCNF.Seed SourceVariable) :
    source.Seeded seed ↔ Problem (reduction seed) :=
  (retainedPolaritySeeded_iff source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty seed).trans
    (PeriodicPlanarOneInThreeToThreeDM.totalSeedReduction_correct fixedFormula
      fixedFormula_occurrences fixedFormula_arity _)

theorem coREHard : CoREHard Problem := by
  intro A _ predicate hs
  obtain ⟨reduce,computed,correct⟩ := FixedThreeSATThreeSeed.coREHard predicate hs
  refine ⟨reduction ∘ reduce,reduction_primrec.to_comp.comp computed,?_⟩
  intro a
  exact (correct a).trans (reduction_correct (reduce a))

theorem coREComplete : CoREComplete Problem := ⟨fixedInstance.prescribed_coRE,coREHard⟩

theorem fixedInstance_eq : fixedInstance =
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem source
      FixedThreeSATThreeSeed.fixedFormula_isLocal
      FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
      FixedThreeSATThreeSeed.fixedFormula_clausesNonempty :=
  retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_eq source
    FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

def fixedPresentation : fixedInstance.ContinuousPlanarPresentation :=
  fixedInstance_eq.symm ▸ retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation source
    FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

open Lean Elab Command in
run_cmd do
  for name in [``coREComplete,``fixedPresentation] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedPlanarThreeDMSeed
