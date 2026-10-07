/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedSeed
import LeanTrominoes.PeriodicCNFSeedWrapping
import LeanTrominoes.PeriodicCNFSeedVariableGauge
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicizationComputability

/-! # Finite prescriptions at the final retained planar-SAT endpoint

The canonical variable gauge shifts the prescribed cell. Clause-anchor
normalization and deduplication leave the decoded assignment unchanged.
-/
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

attribute [local irreducible] retainedDrawingWrappedPeriodicPlanarSATVariableGauge

def retainedGaugedSeedRead (source : PeriodicCNF V) (v : V) :
    PeriodicLiteral (WrappedPeriodicPlanarSATVariable V) :=
  let atom : WrappedPeriodicPlanarSATVariable V := ⟨.atom v⟩
  ⟨atom,retainedDrawingWrappedPeriodicPlanarSATVariableGauge source atom,true⟩

private theorem finalRetained_satisfies_iff (source : PeriodicCNF V)
    (a : WrappedPeriodicPlanarSATVariable V → Cell → Bool) :
    ((wrapPeriodicPlanarSATFormula (retainedDrawingPeriodicPlanarSATFormula source)).variableGauge
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source)).Satisfies a ↔
      (retainedPlanarSATFormula source).Satisfies a := by
  unfold retainedPlanarSATFormula
  rw [retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.deduplicateByLiterals_satisfies_iff,
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_anchorNormalize,PeriodicCNF.anchorNormalize_satisfies_iff,
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]

theorem retainedGaugedSeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) :
    Factor source (retainedPlanarSATFormula source) (retainedGaugedSeedRead source) Set.univ := by
  have first := (retainedSeedFactor source locality width occurrences).compose
    (wrapperFactor (retainedDrawingPeriodicPlanarSATFormula source))
    (fun _ _ => Set.mem_univ _)
  have combined := first.compose
    (gaugeFactor (wrapPeriodicPlanarSATFormula (retainedDrawingPeriodicPlanarSATFormula source))
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source))
    (fun _ _ => Set.mem_univ _)
  have same : compose (compose (@retainedSeedRead V) wrapperRead)
      (gaugeRead (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source)) =
      retainedGaugedSeedRead source := by
    funext v
    simp [compose,retainedSeedRead,wrapperRead,gaugeRead,retainedGaugedSeedRead,Cell.add]
  rw [same] at combined
  exact combined.congrTarget (finalRetained_satisfies_iff source)

theorem retainedGaugedSeeded_iff (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ (retainedPlanarSATFormula source).Seeded
      (transportSeed (retainedGaugedSeedRead source) seed) :=
  (retainedGaugedSeedFactor source locality width occurrences).seeded_iff seed
    (fun _ _ => Set.mem_univ _)

theorem retainedGaugedSeedRead_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (retainedGaugedSeedRead source) := by
  have atom : Primrec (fun v : V => (⟨PeriodicPlanarSATVariable.atom v⟩ : WrappedPeriodicPlanarSATVariable V)) :=
    WrappedPeriodicVariable.mk_primrec.comp PeriodicPlanarSATVariable.atom_primrec
  have gauge : Primrec (fun v : V =>
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge source ⟨.atom v⟩) :=
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_primrec.comp
      (Primrec.pair (Primrec.const source) atom)
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair atom (Primrec.pair gauge (Primrec.const true)))

theorem retainedGaugedSeedReduction_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (transportSeed (retainedGaugedSeedRead source)) :=
  transportSeed_primrec (retainedGaugedSeedRead_primrec source)

open Lean Elab Command in
run_cmd do
  let name := ``retainedGaugedSeedFactor
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicOrthocrossing
