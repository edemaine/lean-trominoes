/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedThreeSATThreeSeedPromises
import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedSeed

/-! # Finite-prescription completeness at one fixed certified planar formula -/
noncomputable section
namespace LeanTrominoes.FixedPlanarSATSeed
open LeanWang PeriodicOrthocrossing PeriodicCNF.SignedDecoder

abbrev SourceVariable := FixedThreeSATThreeSeed.Variable
abbrev Variable := WrappedPeriodicPlanarSATVariable SourceVariable

local instance : DecidableEq Variable := Encodable.decidableEqOfEncodable _

abbrev source := FixedThreeSATThreeSeed.fixedFormula
def fixedFormula : PeriodicCNF Variable := retainedPlanarSATFormula source

private theorem source_occurrences :
    @PeriodicCNF.OccurrencesAtMost SourceVariable instBEqOfDecidableEq (by infer_instance) 3 source := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3 source
    FixedThreeSATThreeSeed.fixedFormula_occurrencesAtMostThree

theorem fixedCertificate : RetainedPlanarSATCertificate source :=
  retainedPlanarSATCertificate source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

def reduction (seed : PeriodicCNF.Seed SourceVariable) : PeriodicCNF.Seed Variable :=
  transportSeed (retainedGaugedSeedRead source) seed

theorem reduction_primrec : Primrec reduction := retainedGaugedSeedReduction_primrec source

theorem reduction_correct (seed : PeriodicCNF.Seed SourceVariable) :
    source.Seeded seed ↔ fixedFormula.Seeded (reduction seed) :=
  retainedGaugedSeeded_iff source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences seed

theorem coREHard : CoREHard fixedFormula.Seeded := by
  intro A _ predicate hs
  obtain ⟨reduce,computed,correct⟩ := FixedThreeSATThreeSeed.coREHard predicate hs
  refine ⟨reduction ∘ reduce,reduction_primrec.to_comp.comp computed,?_⟩
  intro a
  exact (correct a).trans (reduction_correct (reduce a))

theorem coREComplete : CoREComplete fixedFormula.Seeded :=
  ⟨PeriodicCNF.fixed_seeded_coRE fixedFormula,coREHard⟩

open Lean Elab Command in
run_cmd do
  for name in [``fixedCertificate,``coREComplete] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedPlanarSATSeed
