/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedFinalExactOneSeed
import LeanTrominoes.SAT.CNF.PeriodicPolarityRoutedSeed
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDMComputability

/-! # Pin-preserving decoder for the formula consumed by padded planar 3DM -/
noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def retainedPolaritySeedRead (source : PeriodicCNF V) :
    Read V (PolarityNormalizedVariable (RetainedOrderedFixedEightOneInThreeVariable V)) :=
  compose (retainedFinalExactOneSeedRead source) inclusionRead

theorem retainedPolaritySeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    LogicalFactor source.Satisfies
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed source).anchorNormalize)
      (retainedPolaritySeedRead source) Set.univ := by
  have result := (retainedFinalExactOneSeedFactor source locality width occurrences nonempty).compose
    (PeriodicOneInThreePolarityNormalizationRouteSubdivision.seedFactor
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase)
    (fun _ _ => Set.mem_univ _)
  exact result.congrTarget (fun a =>
    (PeriodicOneInThree.anchorNormalize_satisfies_iff
      (retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed source) a).symm)

theorem retainedPolaritySeeded_iff (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ Prescribed
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed source).anchorNormalize)
      (transportSeed (retainedPolaritySeedRead source) seed) :=
  (retainedPolaritySeedFactor source locality width occurrences nonempty).seeded_iff
    seed (fun _ _ => Set.mem_univ _)

theorem retainedPolaritySeedRead_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (retainedPolaritySeedRead source) :=
  compose_primrec (retainedFinalExactOneSeedRead_primrec source) inclusionRead_primrec

open Lean Elab Command in
run_cmd do
  for name in [``retainedPolaritySeedFactor,``retainedPolaritySeedRead_primrec] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicOrthocrossing
