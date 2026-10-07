/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeDMLocality
import LeanTrominoes.PeriodicPlanarExactOneLocality
import LeanTrominoes.PeriodicThreeDMPlaneCompleteness
import Lean.Util.CollectAxioms

/-! # The local plane clause of Theorem 3.7

The input includes a checked continuous planar drawing. Every incidence
edge has Manhattan offset at most one, and every colored vertex has degree
two or three. Malformed inputs are rejected.
-/

namespace LeanTrominoes.PeriodicWangPlanarThreeDMReduction
open PeriodicOrthocrossing
set_option synthInstance.maxSize 2048
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem problem_isLocal (tiles : LeanWang.TileSet) : (problem tiles).IsLocal := by
  unfold problem retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
  apply PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_isLocal
  · exact retainedFinalGaugedFormula_isLocal (sourceFormula tiles)
      (sourceFormula_isLocal tiles) (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles) (sourceFormula_clausesNonempty tiles)
  · intro clause member empty
    have arity := retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
      (sourceFormula tiles) (sourceFormula_isLocal tiles) (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles) (sourceFormula_clausesNonempty tiles)
      clause member
    simp [empty] at arity

end LeanTrominoes.PeriodicWangPlanarThreeDMReduction

namespace LeanTrominoes.PeriodicThreeDM
open Gadget NormalizationCompiler

theorem isLocal_primrec : PrimrecPred IsLocal := by
  have offset : Primrec (fun a : PeriodicThreeDMTriple × WireColor =>
      (a.1.reference a.2).offset) :=
    PeriodicThreeDMReference.offset_primrec.comp triple_reference_primrec
  have bound : PrimrecRel (fun (t : PeriodicThreeDMTriple) (c : WireColor) =>
      (t.reference c).offset.1.natAbs + (t.reference c).offset.2.natAbs ≤ 1) :=
    Primrec.nat_le.comp (Primrec.nat_add.comp
      (int_natAbs_primrec.comp (Primrec.fst.comp offset))
      (int_natAbs_primrec.comp (Primrec.snd.comp offset))) (Primrec.const 1)
  have colors := bound.swap.forall_mem_list.comp (Primrec.const AsCNF.colors) Primrec.id
  have all := colors.forall_mem_list.comp triples_primrec
  apply all.of_eq
  intro p
  constructor
  · intro h t ht c
    exact h t ht c (AsCNF.mem_colors c)
  · intro h t ht c _
    exact h t ht c

def LocalPlaneProblem (i : Input) : Prop := i.problem.IsLocal ∧ PlaneProblem i

theorem localPlaneProblem_coRE : LeanWang.CoREPred LocalPlaneProblem := by
  have checked : PrimrecPred fun i : Input =>
      i.problem.IsLocal ∧ i.problem.IsWellFormed ∧ i.problem.DegreeTwoOrThree ∧
        FiniteDrawingCertificate.verifies i.problem i.drawing = true :=
    (isLocal_primrec.comp Input.problem_primrec).and
      ((isWellFormed_primrec.comp Input.problem_primrec).and
        ((degreeTwoOrThree_primrec.comp Input.problem_primrec).and
          (Primrec.eq.comp (FiniteDrawingCertificate.verifies_primrec.comp
            Input.problem_primrec Input.drawing_primrec) (Primrec.const true))))
  exact (PeriodicCNF.restricted_preimage_coRE checked
    (AsCNF.formula_primrec.comp Input.problem_primrec)).of_eq fun i => by
      apply not_congr
      simp only [LocalPlaneProblem, PlaneProblem, AsCNF.satisfiable_iff, and_assoc]

theorem localPlaneProblem_coREHard : LeanWang.CoREHard LocalPlaneProblem := by
  intro A _ source hs
  obtain ⟨f, hf, correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨PeriodicWangPlanarThreeDMReduction.searchedInput ∘ f,
    PeriodicWangPlanarThreeDMReduction.searchedInput_computable.comp hf, ?_⟩
  intro a
  rw [correct a]
  constructor
  · intro tiled
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_apply, PeriodicWangPlanarThreeDMReduction.searchedInput_problem]
        using PeriodicWangPlanarThreeDMReduction.problem_isLocal (f a)
    · exact ⟨(PeriodicWangPlanarThreeDMReduction.presentation (f a)).problemWellFormed,
        PeriodicWangPlanarThreeDMReduction.problem_degreeTwoOrThree (f a),
        FiniteDrawingSearch.searchDrawing_spec
          PeriodicWangPlanarThreeDMReduction.problem
          PeriodicWangPlanarThreeDMReduction.problem_hasVerifiedDrawing (f a),
        (PeriodicWangPlanarThreeDMReduction.problem_correct (f a)).1 tiled⟩
  · intro h
    exact (PeriodicWangPlanarThreeDMReduction.problem_correct (f a)).2 h.2.2.2.2

theorem localPlaneProblem_coREComplete : LeanWang.CoREComplete LocalPlaneProblem :=
  ⟨localPlaneProblem_coRE, localPlaneProblem_coREHard⟩

open Lean Elab Command in
run_cmd do
  let name := ``localPlaneProblem_coREComplete
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicThreeDM
