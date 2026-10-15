/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationSeedRead
import LeanTrominoes.SAT.CNF.PeriodicBooleanSignedDecoder

/-! # Pin-preserving equivalence between 3DM and its normalized drawing CNF -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.SeedNormalization
open Gadget PeriodicCNF.SignedDecoder
variable {problem : PeriodicThreeDM}

theorem matching_satisfies_of_suppressed (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation) (valid : problem.IsSuppressedOrientation values) :
    problem.Satisfies (fun index c => values ⟨index,.red⟩ c) := by
  have graph := (problem.isGraphOrientation_iff_isSuppressedOrientation degree values).2 valid
  change problem.Satisfies (problem.restrictOrientation (problem.fromGraphOrientation values))
  intro color atom bound c
  rw [incidentValues_lift_restrict problem (problem.fromGraphOrientation values)
    (show problem.TripleCoherent (problem.fromGraphOrientation values) from graph.1)]
  exact graph.2 color atom bound c

theorem formula_satisfies_iff (a : problem.MatchingAssignment) :
    (AsCNF.formula problem).Satisfies a ↔ problem.Satisfies a := by
  rw [AsCNF.formula,PeriodicExactOneCNF.satisfies_iff,AsCNF.exactOne_satisfies]

theorem seedFactor (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree : presentation.toPlanarPresentation.FinalAssignmentsCollisionFree) :
    Factor (AsCNF.formula problem)
      (PeriodicCNF.Reflection.formula
        (Gadget.NormalizedOrientation.AsCNF.formula (drawing presentation.toPlanarPresentation)))
      (read presentation.toPlanarPresentation) {index | index < problem.triples.length} := by
  let planar := presentation.toPlanarPresentation
  let d := drawing planar
  have wellFormed := presentation.problemWellFormed
  constructor
  · intro a ha
    have oriented : d.IsOrientation
        (Gadget.NormalizedOrientation.AsCNF.orientation d (PeriodicCNF.Reflection.assignment a)) :=
      (Gadget.NormalizedOrientation.AsCNF.satisfies_iff d _).1
        ((PeriodicCNF.Reflection.satisfies_iff _ a).1 ha)
    rw [read_decode,formula_satisfies_iff]
    exact matching_satisfies_of_suppressed degree _
      (presentation.reverseGraphOrientation_isSuppressedOrientation
        wellFormed degree collisionFree _ oriented)
  · intro a ha
    have matching := formula_satisfies_iff a |>.1 ha
    let values := problem.toGraphOrientation (problem.liftAssignment a)
    have suppressed : problem.IsSuppressedOrientation values :=
      (problem.isGraphOrientation_iff_isSuppressedOrientation degree values).1
        ⟨fun _ _ _ => ⟨rfl,rfl⟩,matching⟩
    let o := presentation.forwardDrawingOrientation values
    have oriented : d.IsOrientation o :=
      presentation.forwardDrawingOrientation_isOrientation wellFormed degree collisionFree values suppressed
    let b := PeriodicCNF.Reflection.assignment (Gadget.NormalizedOrientation.AsCNF.assignment d o)
    refine ⟨b,?_,?_⟩
    · apply (PeriodicCNF.Reflection.satisfies_iff _ b).2
      rw [show PeriodicCNF.Reflection.assignment b =
        Gadget.NormalizedOrientation.AsCNF.assignment d o by
          exact PeriodicCNF.Reflection.assignment_assignment _]
      exact (Gadget.NormalizedOrientation.AsCNF.assignment_satisfies_iff d o).2 oriented
    · intro index bound c
      rw [read_decode]
      change planar.reverseGraphOrientation
        (Gadget.NormalizedOrientation.AsCNF.orientation d (PeriodicCNF.Reflection.assignment b))
        ⟨index,.red⟩ c = a index c
      rw [show PeriodicCNF.Reflection.assignment b =
        Gadget.NormalizedOrientation.AsCNF.assignment d o by
          exact PeriodicCNF.Reflection.assignment_assignment _,
        Gadget.NormalizedOrientation.AsCNF.orientation_assignment]
      exact forward_inverse presentation wellFormed degree collisionFree values index bound c

open Lean Elab Command in
run_cmd do
  for name in [``seedFactor,``forward_inverse] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicThreeDM.SeedNormalization
