/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMNormalizationSeedFactor
import LeanTrominoes.PeriodicBooleanSeedSupport

/-! # Computable finite tables for normalized matching-bit decoders -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.SeedNormalization
open Gadget PeriodicCNF.SignedDecoder
variable {problem : PeriodicThreeDM}

def defaultRead : PeriodicLiteral Gadget.NormalizedOrientation.AsCNF.Variable :=
  ⟨((0,0),.north),(0,0),false⟩

def boundedRead (presentation : problem.PlanarPresentation) (index : Nat) :
    PeriodicLiteral Gadget.NormalizedOrientation.AsCNF.Variable :=
  ((List.range problem.triples.length).map (read presentation)).getD index defaultRead

theorem boundedRead_eq (presentation : problem.PlanarPresentation) (index : Nat)
    (bound : index < problem.triples.length) : boundedRead presentation index = read presentation index := by
  simp [boundedRead,List.getD,List.getElem?_map,List.getElem?_range bound]

theorem boundedRead_primrec (presentation : problem.PlanarPresentation) : Primrec (boundedRead presentation) :=
  (Primrec.list_getD defaultRead).comp
    (Primrec.const ((List.range problem.triples.length).map (read presentation))) Primrec.id

theorem matching_stable_on_indices (a b : problem.MatchingAssignment)
    (same : ∀ index < problem.triples.length, ∀ c, a index c = b index c) :
    problem.Satisfies a ↔ problem.Satisfies b := by
  have values (color : WireColor) (atom : Nat) (c : Cell) :
      problem.incidentValues (problem.liftAssignment a) color atom c =
        problem.incidentValues (problem.liftAssignment b) color atom c := by
    apply List.map_congr_left
    intro incidence member
    exact same incidence.tripleIndex (incidence_tripleIndex_lt problem color atom member) _
  constructor <;> intro valid color atom bound c
  · rw [← values]
    exact valid color atom bound c
  · rw [values]
    exact valid color atom bound c

theorem boundedSeedFactor (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree : presentation.toPlanarPresentation.FinalAssignmentsCollisionFree) :
    Factor (AsCNF.formula problem)
      (PeriodicCNF.Reflection.formula
        (Gadget.NormalizedOrientation.AsCNF.formula (drawing presentation.toPlanarPresentation)))
      (boundedRead presentation.toPlanarPresentation) {index | index < problem.triples.length} := by
  have original := seedFactor presentation degree collisionFree
  have same (a : Gadget.NormalizedOrientation.AsCNF.Variable → Cell → Bool)
      (index : Nat) (bound : index < problem.triples.length) (c : Cell) :
      decode (read presentation.toPlanarPresentation) a index c =
        decode (boundedRead presentation.toPlanarPresentation) a index c := by
    simp only [decode,boundedRead_eq presentation.toPlanarPresentation index bound]
  constructor
  · intro a ha
    apply (formula_satisfies_iff _).2
    exact (matching_stable_on_indices _ _ (same a)).1
      ((formula_satisfies_iff _).1 (original.sound a ha))
  · intro a ha
    obtain ⟨b,hb,inverse⟩ := original.complete a ha
    refine ⟨b,hb,?_⟩
    intro index bound c
    exact (same b index bound c).symm.trans (inverse index bound c)

def totalSeedReduction (presentation : problem.PlanarPresentation) :
    PeriodicCNF.Seed Nat → PeriodicCNF.Seed Gadget.NormalizedOrientation.AsCNF.Variable :=
  supportedReduction (List.range problem.triples.length) (boundedRead presentation) ((0,0),.north)

theorem totalSeedReduction_primrec (presentation : problem.PlanarPresentation) :
    Primrec (totalSeedReduction presentation) :=
  supportedReduction_primrec _ (boundedRead_primrec presentation) _

theorem totalSeedReduction_correct (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree : presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (seed : PeriodicCNF.Seed Nat) :
    Prescribed problem.Satisfies seed ↔
      (PeriodicCNF.Reflection.formula
        (Gadget.NormalizedOrientation.AsCNF.formula (drawing presentation.toPlanarPresentation))).Seeded
        (totalSeedReduction presentation.toPlanarPresentation seed) := by
  have factor : LogicalFactor problem.Satisfies
      (PeriodicCNF.Reflection.formula
        (Gadget.NormalizedOrientation.AsCNF.formula (drawing presentation.toPlanarPresentation))).Satisfies
      (boundedRead presentation.toPlanarPresentation) {index | index ∈ List.range problem.triples.length} := by
    have original := boundedSeedFactor presentation degree collisionFree
    constructor
    · intro a ha
      exact (formula_satisfies_iff _).1 (original.sound a ha)
    · intro a ha
      obtain ⟨b,hb,inverse⟩ := original.complete a ((formula_satisfies_iff _).2 ha)
      exact ⟨b,hb,fun index member c => inverse index (List.mem_range.mp member) c⟩
  exact supportedReduction_correct _ _ factor
    (fun a b same => matching_stable_on_indices a b
      (fun index bound c => same index (List.mem_range.mpr bound) c)) seed

open Lean Elab Command in
run_cmd do
  for name in [``boundedSeedFactor,``totalSeedReduction_correct,``totalSeedReduction_primrec] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicThreeDM.SeedNormalization
