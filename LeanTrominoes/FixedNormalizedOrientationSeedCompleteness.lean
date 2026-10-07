/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPlanarThreeDMSeedGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationBoundedSeedFactor

/-! # Finite-seed completeness for one fixed normalized orthogonal drawing -/
noncomputable section
namespace LeanTrominoes.FixedNormalizedOrientationSeed
open LeanWang Gadget PeriodicCNF.SignedDecoder

abbrev Variable := Gadget.NormalizedOrientation.AsCNF.Variable
def fixedDrawing : PeriodicOrthogonalDrawing :=
  FixedPlanarThreeDMSeed.fixedPresentation.toPlanarPresentation.normalizedOrthogonalDrawing
def fixedFormula : PeriodicCNF Variable :=
  PeriodicCNF.Reflection.formula (Gadget.NormalizedOrientation.AsCNF.formula fixedDrawing)
def Problem := fixedFormula.Seeded

def reduction : PeriodicCNF.Seed Nat → PeriodicCNF.Seed Variable :=
  PeriodicThreeDM.SeedNormalization.totalSeedReduction
    FixedPlanarThreeDMSeed.fixedPresentation.toPlanarPresentation

theorem reduction_primrec : Primrec reduction :=
  PeriodicThreeDM.SeedNormalization.totalSeedReduction_primrec _

theorem reduction_correct (seed : PeriodicCNF.Seed Nat) :
    FixedPlanarThreeDMSeed.Problem seed ↔ Problem (reduction seed) :=
  PeriodicThreeDM.SeedNormalization.totalSeedReduction_correct
    FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance_degree
    FixedPlanarThreeDMSeed.fixedPresentation_collisionFree seed

theorem coREHard : CoREHard Problem := by
  intro A _ predicate hs
  obtain ⟨reduce,computed,correct⟩ := FixedPlanarThreeDMSeed.coREHard predicate hs
  refine ⟨reduction ∘ reduce,reduction_primrec.to_comp.comp computed,?_⟩
  intro a
  exact (correct a).trans (reduction_correct (reduce a))

theorem coREComplete : CoREComplete Problem :=
  ⟨PeriodicCNF.fixed_seeded_coRE fixedFormula,coREHard⟩

theorem fixedDrawing_wellFormed : fixedDrawing.IsWellFormed :=
  FixedPlanarThreeDMSeed.fixedDrawing_wellFormed

theorem fixedDrawing_verticesSeparated : fixedDrawing.VerticesSeparated :=
  FixedPlanarThreeDMSeed.fixedDrawing_verticesSeparated

open Lean Elab Command in
run_cmd do
  for name in [``coREComplete,``fixedDrawing_wellFormed,``fixedDrawing_verticesSeparated] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedNormalizedOrientationSeed
