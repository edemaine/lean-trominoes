/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMCNF
import LeanTrominoes.PeriodicCNFPreimageCoRE
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Plane 3DM completeness with verified periodic drawings -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget NormalizationCompiler

private theorem all_primrec {A B : Type} [Primcodable A] [Primcodable B]
    {xs : A → List B} {p : A → B → Prop}
    (hx : Primrec xs) (hp : PrimrecRel p) :
    PrimrecPred (fun a => ∀ b ∈ xs a, p a b) :=
  hp.swap.forall_mem_list.comp hx Primrec.id

theorem isWellFormed_primrec : PrimrecPred IsWellFormed := by
  have ref : PrimrecRel fun (p : PeriodicThreeDM × PeriodicThreeDMTriple) (c : WireColor) =>
      (p.2.reference c).atom < p.1.elementCount c :=
    Primrec.nat_lt.comp
      (PeriodicThreeDMReference.atom_primrec.comp
        (triple_reference_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (elementCount_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have row := all_primrec (Primrec.const AsCNF.colors) ref
  have all := all_primrec triples_primrec row.primrecRel
  apply all.of_eq
  intro p
  constructor
  · intro h t ht c; exact h t ht c (AsCNF.mem_colors c)
  · intro h t ht c _; exact h t ht c

theorem degreeTwoOrThree_primrec : PrimrecPred DegreeTwoOrThree := by
  have bound : PrimrecPred fun p : (PeriodicThreeDM × WireColor) × Nat =>
      p.1.1.degree p.1.2 p.2 ∈ ([2,3] : List Nat) :=
    PeriodicCNF.FiniteSearch.mem_primrec.comp degree_primrec (Primrec.const [2,3])
  have row := all_primrec (Primrec.list_range.comp elementCount_primrec) bound.primrecRel
  have all := all_primrec (Primrec.const AsCNF.colors) row.primrecRel
  apply all.of_eq
  intro p
  constructor
  · intro h c v hv; exact h c (AsCNF.mem_colors c) v (List.mem_range.mpr hv)
  · intro h c _ v hv; exact h c v (List.mem_range.mp hv)

/-- Input includes a finite drawing. Invalid drawings and malformed problems
are no-instances; the colored degree restriction is part of the predicate. -/
def PlaneProblem (i : Input) : Prop :=
  i.problem.IsWellFormed ∧ i.problem.DegreeTwoOrThree ∧
    FiniteDrawingCertificate.verifies i.problem i.drawing = true ∧ i.problem.Satisfiable

theorem planeProblem_coRE : LeanWang.CoREPred PlaneProblem := by
  have checked : PrimrecPred fun i : Input =>
      i.problem.IsWellFormed ∧ i.problem.DegreeTwoOrThree ∧
        FiniteDrawingCertificate.verifies i.problem i.drawing = true :=
    (isWellFormed_primrec.comp Input.problem_primrec).and
      ((degreeTwoOrThree_primrec.comp Input.problem_primrec).and
        (Primrec.eq.comp (FiniteDrawingCertificate.verifies_primrec.comp
          Input.problem_primrec Input.drawing_primrec) (Primrec.const true)))
  have upper := PeriodicCNF.restricted_preimage_coRE checked
    (AsCNF.formula_primrec.comp Input.problem_primrec)
  exact upper.of_eq fun i => by
    apply not_congr
    simp only [PlaneProblem, AsCNF.satisfiable_iff, and_assoc]

theorem planeProblem_coREHard : LeanWang.CoREHard PlaneProblem := by
  intro A _ source hs
  obtain ⟨f, hf, correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨PeriodicWangPlanarThreeDMReduction.searchedInput ∘ f,
    PeriodicWangPlanarThreeDMReduction.searchedInput_computable.comp hf, ?_⟩
  intro a
  rw [correct a]
  simp only [Function.comp_apply, PlaneProblem,
    PeriodicWangPlanarThreeDMReduction.searchedInput_problem,
    PeriodicWangPlanarThreeDMReduction.searchedInput_drawing]
  constructor
  · intro tiled
    exact ⟨(PeriodicWangPlanarThreeDMReduction.presentation (f a)).problemWellFormed,
      PeriodicWangPlanarThreeDMReduction.problem_degreeTwoOrThree (f a),
      FiniteDrawingSearch.searchDrawing_spec
        PeriodicWangPlanarThreeDMReduction.problem
        PeriodicWangPlanarThreeDMReduction.problem_hasVerifiedDrawing (f a),
      (PeriodicWangPlanarThreeDMReduction.problem_correct (f a)).1 tiled⟩
  · intro h
    exact (PeriodicWangPlanarThreeDMReduction.problem_correct (f a)).2 h.2.2.2

/-- Plane periodic 3DM is co-r.e. complete with a checked orthogonal planar
presentation and degree two or three at every colored vertex. -/
theorem planeProblem_coREComplete : LeanWang.CoREComplete PlaneProblem :=
  ⟨planeProblem_coRE, planeProblem_coREHard⟩

/-- A positive instance carries genuine continuous planarity, not just an
unchecked drawing annotation. -/
theorem planeProblem_hasPresentation {i : Input} (h : PlaneProblem i) :
    Nonempty i.problem.ContinuousPlanarPresentation :=
  ⟨(FiniteDrawingCertificate.certifiedPresentationOfVerified h.1 h.2.2.1).presentation⟩

end LeanTrominoes.PeriodicThreeDM
