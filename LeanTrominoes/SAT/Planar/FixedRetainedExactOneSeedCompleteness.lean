/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FixedPlanarSATSeedCompleteness
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedFinalExactOneSeed
import LeanTrominoes.SAT.Planar.PeriodicPlanarExactOneEndpoint
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneSeededCoRE

/-! # Finite-prescription completeness for one fixed retained exact-one formula -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedRetainedExactOneSeed
open LeanWang PeriodicOrthocrossing PeriodicCNF.SignedDecoder

abbrev SourceVariable := FixedThreeSATThreeSeed.Variable
abbrev Variable := RetainedOrderedFixedEightOneInThreeVariable SourceVariable
local instance : DecidableEq Variable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

abbrev source := FixedThreeSATThreeSeed.fixedFormula
def fixedFormula : PeriodicCNF Variable :=
  (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase
def Problem := Prescribed (PeriodicOneInThree.Satisfies fixedFormula)

private theorem source_occurrences :
    @PeriodicCNF.OccurrencesAtMost SourceVariable instBEqOfDecidableEq (by infer_instance) 3 source :=
  PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 source
    FixedThreeSATThreeSeed.fixedFormula_occurrencesAtMostThree

def reduction (seed : PeriodicCNF.Seed SourceVariable) : PeriodicCNF.Seed Variable :=
  transportSeed (retainedFinalExactOneSeedRead source) seed

theorem reduction_primrec : Primrec reduction :=
  transportSeed_primrec (retainedFinalExactOneSeedRead_primrec source)

theorem reduction_correct (seed : PeriodicCNF.Seed SourceVariable) :
    source.Seeded seed ↔ Problem (reduction seed) :=
  retainedFinalExactOneSeeded_iff source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty seed

def fixedDrawing : PeriodicGridDrawing := PeriodicPlanarSAT.ExactOneEndpoint.drawing source

theorem fixedDrawing_planar : fixedDrawing.IsContinuouslyPlanar :=
  PeriodicPlanarSAT.ExactOneEndpoint.planar source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem fixedDrawing_compatible : fixedDrawing.IsCompatible fixedFormula.incidenceGraph :=
  PeriodicPlanarSAT.ExactOneEndpoint.compatible source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem coREHard : CoREHard Problem := by
  intro A _ predicate hs
  obtain ⟨reduce,computed,correct⟩ := FixedThreeSATThreeSeed.coREHard predicate hs
  refine ⟨reduction ∘ reduce,reduction_primrec.to_comp.comp computed,?_⟩
  intro a
  exact (correct a).trans (reduction_correct (reduce a))

theorem coREComplete : CoREComplete Problem :=
  ⟨PeriodicExactOneCNF.fixed_seeded_coRE fixedFormula,coREHard⟩

open Lean Elab Command in
run_cmd do
  for name in [``coREComplete,``fixedDrawing_planar,``fixedDrawing_compatible] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedRetainedExactOneSeed
