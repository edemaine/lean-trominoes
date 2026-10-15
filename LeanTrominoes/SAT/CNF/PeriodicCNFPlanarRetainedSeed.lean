/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoderComposition
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedPeriodicSoundness
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarPeriodicizationComputability

/-! # Retained planarization preserves prescribed source Boolean values -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def retainedSeedRead (atom : V) : PeriodicLiteral (PeriodicPlanarSATVariable V) :=
  ⟨.atom atom,(0,0),true⟩

omit [DecidableEq V] in
theorem retainedSeedRead_decode (a : PeriodicPlanarSATVariable V → Cell → Bool) :
    decode retainedSeedRead a = sourceAssignmentOfPeriodicPlanarSAT a := by
  funext v c
  simp [decode,retainedSeedRead,sourceAssignmentOfPeriodicPlanarSAT,Cell.add]

theorem retainedSeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) :
    Factor source (retainedDrawingPeriodicPlanarSATFormula source) retainedSeedRead Set.univ := by
  constructor
  · intro a ha
    rw [retainedSeedRead_decode]
    exact satisfies_of_retainedDrawingPeriodicPlanarSATFormula_satisfies source
      (PeriodicCNF.incidenceGraph_isWellFormed source)
      (PeriodicCNF.incidenceGraph_degreeAtMost width occurrences)
      (PeriodicCNF.incidenceGraph_isLocal locality) occurrences a ha
  · intro a ha
    refine ⟨periodicPlanarSATAssignment source a ha,
      retainedDrawingPeriodicPlanarSATFormula_satisfies_of_satisfies source a ha,?_⟩
    intro v _ c
    simp [decode,retainedSeedRead,periodicPlanarSATAssignment,Cell.add]

theorem retainedSeeded_iff (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ (retainedDrawingPeriodicPlanarSATFormula source).Seeded
      (transportSeed retainedSeedRead seed) :=
  (retainedSeedFactor source locality width occurrences).seeded_iff seed (fun _ _ => Set.mem_univ _)

omit [DecidableEq V] in
theorem retainedSeedRead_primrec [Primcodable V] : Primrec (@retainedSeedRead V) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair PeriodicPlanarSATVariable.atom_primrec (Primrec.const ((0,0),true)))

omit [DecidableEq V] in
theorem retainedSeedReduction_primrec [Primcodable V] :
    Primrec (transportSeed (@retainedSeedRead V)) :=
  transportSeed_primrec retainedSeedRead_primrec

open Lean Elab Command in
run_cmd do
  let name := ``retainedSeedFactor
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicOrthocrossing
