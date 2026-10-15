/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Results
import LeanTrominoes.SAT.Results
import LeanTrominoes.ThreeDM.Results
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATInjectiveRenaming
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralDrawing
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalization

/-! # Proof bridge for the graph and constraint abstract

The native finite input records and encodings are retained. Thus changing a
predicate to its expanded mathematical definition requires no input conversion.
The only representation change below replaces auxiliary variable names by
natural numbers; its primitive-recursive certificate is used in every transfer.
This module does not import `GraphAbstract`.
-/

namespace LeanTrominoes.GraphAbstractBridge

theorem coRE_congr {A : Type} [Primcodable A] {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : LeanWang.CoREComplete p) : LeanWang.CoREComplete q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

theorem pspace_congr {A : Type} {e : FiniteEncoding A} {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : Complexity.PSPACEComplete e p) :
    Complexity.PSPACEComplete e q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

theorem np_congr {A : Type} {e : FiniteEncoding A} {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : Complexity.NPComplete e p) :
    Complexity.NPComplete e q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

private theorem coRE_transport {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} {q : B → Prop} (hp : LeanWang.CoREComplete p)
    (hq : LeanWang.CoREPred q) (f : A → B) (hf : Computable f)
    (correct : ∀ a, p a ↔ q (f a)) : LeanWang.CoREComplete q := by
  refine ⟨hq, ?_⟩
  intro C _ r hr
  obtain ⟨g, hg, h⟩ := hp.2 r hr
  exact ⟨f ∘ g, hf.comp hg, fun c => (h c).trans (correct (g c))⟩

theorem rename_nat_primrec {V : Type} [Primcodable V] :
    Primrec (PeriodicCNF.rename (Encodable.encode : V → Nat)) := by
  have literal : Primrec (PeriodicLiteral.rename (Encodable.encode : V → Nat)) :=
    PeriodicLiteral.equivData_symm_primrec.comp
      ((Primrec.pair (Primrec.encode.comp Primrec.fst) Primrec.snd).comp
        PeriodicLiteral.equivData_primrec)
  have clause := Primrec.list_map Primrec.id (literal.comp Primrec.snd).to₂
  exact PeriodicCNF.equivData_symm_primrec.comp
    ((Primrec.list_map Primrec.id (clause.comp Primrec.snd).to₂).comp PeriodicCNF.equivData_primrec)

theorem planar_rename_nat_primrec {V : Type} [Primcodable V] :
    Primrec (PeriodicPlanarSAT.renameInput (Encodable.encode : V → Nat)) :=
  Primrec.pair (rename_nat_primrec.comp Primrec.fst) Primrec.snd

theorem distance_sum (d : Nat) (a b : Fin d → Int) :
    PeriodicCNFDimensions.distance d a b = ∑ i, (a i-b i).natAbs := by
  induction d with
  | zero => simp [PeriodicCNFDimensions.distance]
  | succ d ih => simp [PeriodicCNFDimensions.distance, Fin.sum_univ_succ, ih]

theorem higher_local_sat (d : Nat) (dimension : 2 ≤ d) : LeanWang.CoREComplete
    (fun f : PeriodicCNFDimensions.Formula d =>
      (∀ c ∈ f, ∀ l ∈ c, ∀ r ∈ c, ∑ i, (l.1.2 i-r.1.2 i).natAbs ≤ 1) ∧
        PeriodicConstraints.Satisfiable (Fin d → Int) f) := by
  apply coRE_congr _ (PeriodicCNFDimensions.localProblem_coREComplete dimension)
  intro f
  simp only [PeriodicCNFDimensions.LocalProblem, PeriodicCNFDimensions.IsLocal, distance_sum]

theorem planar_plane_sat : LeanWang.CoREComplete
    (PeriodicPlanarSAT.Orbit.BoundedLocalProblem (V := Nat)) := by
  classical
  apply coRE_transport PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction.boundedLocalCoREComplete
    PeriodicPlanarSAT.Orbit.boundedLocalProblem_coRE
    (PeriodicPlanarSAT.renameInput Encodable.encode) planar_rename_nat_primrec.to_comp
  intro i
  simp only [PeriodicPlanarSAT.Orbit.BoundedLocalProblem, PeriodicPlanarSAT.Orbit.LocalProblem,
    PeriodicPlanarSAT.Orbit.Problem, PeriodicPlanarSAT.Orbit.Valid,
    PeriodicPlanarSAT.GridBound, PeriodicCNF.presentationSize_rename, PeriodicPlanarSAT.renameInput,
    PeriodicCNF.local_rename, PeriodicCNF.width_rename,
    PeriodicCNF.orbitCompatible_rename _ Encodable.encode_injective,
    PeriodicCNF.satisfiable_rename_iff _ _ Encodable.encode_injective]
  apply Iff.of_eq
  congr
  exact Subsingleton.elim _ _

private theorem planar_plane_three_sat_native : LeanWang.CoREComplete
    (PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem (V := Nat)) := by
  classical
  apply coRE_transport PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction.boundedLocalThreeOccurrenceCoREComplete
    PeriodicPlanarSAT.Orbit.boundedLocalThreeOccurrenceProblem_coRE
    (PeriodicPlanarSAT.renameInput Encodable.encode) planar_rename_nat_primrec.to_comp
  intro i
  simp only [PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.LocalThreeOccurrenceProblem, PeriodicPlanarSAT.Orbit.ThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.Problem, PeriodicPlanarSAT.Orbit.Valid,
    PeriodicPlanarSAT.GridBound, PeriodicCNF.presentationSize_rename, PeriodicPlanarSAT.renameInput,
    PeriodicCNF.local_rename, PeriodicCNF.width_rename,
    PeriodicCNF.occurrences_rename_iff _ Encodable.encode_injective,
    PeriodicCNF.orbitCompatible_rename _ Encodable.encode_injective,
    PeriodicCNF.satisfiable_rename_iff _ _ Encodable.encode_injective]
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

theorem planar_plane_exact_one : LeanWang.CoREComplete
    (PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem (V := Nat)) := by
  classical
  apply coRE_transport PeriodicPlanarSAT.ExactOneEndpoint.WangReduction.boundedLocalCoREComplete
    PeriodicPlanarSAT.Unbounded.boundedLocalExactOneProblem_coRE
    (PeriodicPlanarSAT.renameInput Encodable.encode) planar_rename_nat_primrec.to_comp
  intro i
  simp only [PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneProblem, PeriodicPlanarSAT.Unbounded.ExactOneProblem,
    PeriodicPlanarSAT.Unbounded.Valid, PeriodicPlanarSAT.GridBound, PeriodicCNF.presentationSize_rename, PeriodicPlanarSAT.renameInput,
    PeriodicCNF.local_rename, PeriodicCNF.width_rename,
    PeriodicCNF.finiteCompatible_rename _ Encodable.encode_injective,
    PeriodicOneInThree.satisfiable_rename_iff _ _ Encodable.encode_injective]
  apply Iff.of_eq
  congr
  exact Subsingleton.elim _ _

private theorem planar_plane_exact_one_three_native : LeanWang.CoREComplete
    (PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (V := Nat)) := by
  classical
  apply coRE_transport PeriodicPlanarSAT.ExactOneEndpoint.WangReduction.boundedLocalThreeOccurrenceCoREComplete
    PeriodicPlanarSAT.Unbounded.boundedLocalExactOneThreeOccurrenceProblem_coRE
    (PeriodicPlanarSAT.renameInput Encodable.encode) planar_rename_nat_primrec.to_comp
  intro i
  simp only [PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.ExactOneThreeOccurrenceProblem, PeriodicPlanarSAT.Unbounded.ExactOneProblem,
    PeriodicPlanarSAT.Unbounded.Valid, PeriodicPlanarSAT.GridBound, PeriodicCNF.presentationSize_rename, PeriodicPlanarSAT.renameInput,
    PeriodicCNF.local_rename, PeriodicCNF.width_rename,
    PeriodicCNF.occurrences_rename_iff _ Encodable.encode_injective,
    PeriodicCNF.finiteCompatible_rename _ Encodable.encode_injective,
    PeriodicOneInThree.satisfiable_rename_iff _ _ Encodable.encode_injective]
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

theorem planar_plane_three_sat : LeanWang.CoREComplete
    (fun i : PeriodicPlanarSAT.Input Nat => i.1.OccurrencesAtMost 3 ∧
      PeriodicPlanarSAT.Orbit.BoundedLocalProblem i) := by
  apply coRE_congr _ planar_plane_three_sat_native
  intro i
  simp only [PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.BoundedLocalProblem, PeriodicPlanarSAT.Orbit.LocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.LocalProblem, PeriodicPlanarSAT.Orbit.ThreeOccurrenceProblem,
    and_left_comm]

theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i : PeriodicPlanarSAT.Input Nat => i.1.OccurrencesAtMost 3 ∧
      PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem i) := by
  apply coRE_congr _ planar_plane_exact_one_three_native
  intro i
  simp only [PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneProblem, PeriodicPlanarSAT.Unbounded.ExactOneThreeOccurrenceProblem,
    and_left_comm]

theorem planar_line_three_sat : Complexity.PSPACEComplete PeriodicPlanarSAT.FlatEncoding.finEncoding
    (fun i : PeriodicPlanarSAT.Input Nat => i.1.OccurrencesAtMost 3 ∧
      PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem i) := by
  apply pspace_congr _ PeriodicPlanarSAT.ordinaryThree_PSPACEComplete
  intro i
  simp only [PeriodicPlanarSAT.Orbit.LocalOneDimensionalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem, PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.BoundedLocalProblem, PeriodicPlanarSAT.Orbit.LocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.LocalProblem, PeriodicPlanarSAT.Orbit.ThreeOccurrenceProblem,
    and_left_comm]

theorem planar_line_exact_one_three : Complexity.PSPACEComplete PeriodicPlanarSAT.FlatEncoding.finEncoding
    (fun i : PeriodicPlanarSAT.Input Nat => i.1.OccurrencesAtMost 3 ∧
      PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem i) := by
  apply pspace_congr _ PeriodicPlanarSAT.exactOneThree_PSPACEComplete
  intro i
  simp only [PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneProblem, PeriodicPlanarSAT.Unbounded.ExactOneThreeOccurrenceProblem,
    and_left_comm]

private theorem count_as_decide {A : Type} [DecidableEq A] [BEq A] [LawfulBEq A]
    (a : A) (xs : List A) : xs.count a = xs.countP (fun x => decide (x = a)) := by
  rw [List.count_eq_countP]
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]

theorem plane_three_sat : LeanWang.CoREComplete
    (fun f : PeriodicCNF Nat => f.IsLocal ∧ f.WidthAtMost 3 ∧ f.Satisfiable) := by
  apply coRE_transport PeriodicThreeCNF.localThreeCNFCoREComplete
    (by simpa only [LeanWang.CoREPred, and_assoc] using
      PeriodicCNF.restricted_coRE (PeriodicCNF.isLocal_primrec.and (PeriodicCNF.widthAtMost_primrec 3)))
    (PeriodicCNF.rename Encodable.encode) rename_nat_primrec.to_comp
  intro f
  simp only [PeriodicThreeCNF.LocalThreeCNFHolds, PeriodicCNF.local_rename,
    PeriodicCNF.width_rename, PeriodicCNF.satisfiable_rename_iff _ _ Encodable.encode_injective]

theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f : PeriodicCNF Nat =>
      f.IsLocal ∧ f.WidthAtMost 3 ∧ f.OccurrencesAtMost 3 ∧ f.Satisfiable) := by
  classical
  apply coRE_transport PeriodicThreeSATThree.localThreeSATThreeCoREComplete
    (by simpa only [LeanWang.CoREPred, and_assoc] using
      PeriodicCNF.restricted_coRE (PeriodicCNF.isLocal_primrec.and
        ((PeriodicCNF.widthAtMost_primrec 3).and (PeriodicCNF.occurrencesAtMost_primrec 3))))
    (PeriodicCNF.rename Encodable.encode) rename_nat_primrec.to_comp
  intro f
  simp only [PeriodicThreeSATThree.LocalThreeSATThreeHolds, PeriodicCNF.local_rename,
    PeriodicCNF.width_rename, PeriodicCNF.occurrences_rename_iff _ Encodable.encode_injective,
    PeriodicCNF.satisfiable_rename_iff _ _ Encodable.encode_injective]
  simp only [PeriodicCNF.OccurrencesAtMost, count_as_decide]

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f : PeriodicCNF Nat =>
      f.IsLocal ∧ f.WidthAtMost 3 ∧ f.OccurrencesAtMost 3 ∧ PeriodicOneInThree.Satisfiable f) := by
  classical
  apply coRE_transport PeriodicOneInThree.localOneInThreeSATThreeCoREComplete
    (by simpa only [LeanWang.CoREPred, and_assoc] using
      PeriodicOneInThree.restricted_satisfiable_coRE (PeriodicCNF.isLocal_primrec.and
        ((PeriodicCNF.widthAtMost_primrec 3).and (PeriodicCNF.occurrencesAtMost_primrec 3))))
    (PeriodicCNF.rename Encodable.encode) rename_nat_primrec.to_comp
  intro f
  simp only [PeriodicOneInThree.LocalOneInThreeSATThreeHolds, PeriodicCNF.local_rename,
    PeriodicCNF.width_rename, PeriodicCNF.occurrences_rename_iff _ Encodable.encode_injective,
    PeriodicOneInThree.satisfiable_rename_iff _ _ Encodable.encode_injective]
  simp only [PeriodicCNF.OccurrencesAtMost, count_as_decide]

export PeriodicGridDrawing (polygonal_cubic_refinement)
export GeneralVertexNormalization (lemma23)
export PeriodicOrthocrossing.GeneralPorts (local_orthocrossing_drawing local_orthogonal_orthocrossing_drawing)
export PeriodicLatticeGraph (bounded_augmenting_path bipartition_two_periodic)
export PeriodicBipartite (perfect_iff_quotient exists_period_one perfect_or_short_augmenting
  matchingSolver_certified matchingSolver_edge_sqrt_bound)
export PeriodicCNF.PolySpaceHardness (localPeriodicCNF1DSAT_PSPACEComplete
  localPeriodicThreeCNF1DSAT_PSPACEComplete localPeriodicThreeSATThree1DSAT_PSPACEComplete)
export PeriodicExactOneCNF (localOneDimensionalThreeSAT_PSPACEComplete
  localOneDimensionalThreeSATThree_PSPACEComplete)
export PeriodicCNFDimensions (satisfiable_coREComplete localProblem_coREComplete)
export PeriodicPlanarSAT (ordinary_PSPACEComplete ordinaryThree_PSPACEComplete
  exactOne_PSPACEComplete exactOneThree_PSPACEComplete)
export PeriodicTwoSAT (local_certified)
export Horn (exists_period_one dual_exists_period_one)
export Horn.PeriodicIndexed (certified)
export FiniteCNF (threeSatisfiable_npHard)
export PeriodicThreeDM (localPlaneProblem_coREComplete localLineProblem_PSPACEComplete
  localPlanarLineProblem_PSPACEComplete)
export TrichromaticGraphOrientation (problem_coREComplete finiteProblem_npComplete)

theorem orientation_plane : LeanWang.CoREComplete TrichromaticGraphOrientation.LocalProblem :=
  TrichromaticGraphOrientation.localProblem_coREComplete

theorem orientation_line : Complexity.PSPACEComplete
    TrichromaticGraphOrientation.FlatEncoding.finEncoding
    TrichromaticGraphOrientation.LocalLineProblem :=
  TrichromaticGraphOrientation.localLineProblem_PSPACEComplete

end LeanTrominoes.GraphAbstractBridge
