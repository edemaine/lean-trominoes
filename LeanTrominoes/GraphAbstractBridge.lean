/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstractBridge
import LeanTrominoes.Graphs.Results
import LeanTrominoes.SAT.Results
import LeanTrominoes.ThreeDM.Results
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATInjectiveRenaming
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralDrawing
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalization

/-! # Proof bridge for the graph and constraint abstract

The bridge translates the public graph and drawing data into native records
and proves that the geometric predicates agree. Complexity transfers preserve
the input encodings and use checked computability or machine certificates.
This module does not import `GraphAbstract`.
-/

namespace LeanTrominoes.GraphAbstractBridge

namespace Native

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

/-- The finite Cook–Levin output has the same encoding as its zero-offset
periodic embedding, so the existing polynomial-time machine transfers unchanged. -/
theorem zero_dimensional_sat : Complexity.NPHard PeriodicCNFFlatEncoding.finEncoding
    (fun f : PeriodicCNF Nat => FiniteCNF.ZeroOffsets f ∧ f.WidthAtMost 3 ∧ f.Satisfiable) := by
  intro Input encoding language member
  obtain ⟨verifier⟩ := member
  apply Complexity.PolyTimeManyOneReducible.of_computableInPolyTime
    (fun input => FiniteCNF.periodize (verifier.separatedRequest input).compile)
  · exact ⟨TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      verifier.finiteCNFComputableInPolyTime (fun _ => rfl)⟩
  · intro input
    constructor
    · intro truth
      exact ⟨FiniteCNF.periodize_zeroOffsets _,
        (FiniteCNF.width_periodize _ _).mpr (verifier.separatedRequest_width input),
        (FiniteCNF.satisfiable_periodize _).mpr ((verifier.separatedRequest_correct input).mpr truth)⟩
    · intro truth
      exact (verifier.separatedRequest_correct input).mp
        ((FiniteCNF.satisfiable_periodize _).mp truth.2.2)

/-- Keep only the drawing and size guarantees stated in the abstract. -/
theorem orthocrossing_drawing {V : Type} [DecidableEq V] {g : PeriodicGraph V}
    (valid : g.IsWellFormed) (locality : g.IsLocal) :
    ∃ d : PeriodicGridDrawing, d.IsRealDrawing g ∧ d.IsRealLocal g ∧ d.IsRealOrthocrossing ∧
      d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d, h, hl, hc, hb, _⟩ :=
    PeriodicOrthocrossing.GeneralPorts.local_orthocrossing_drawing valid locality
  exact ⟨d, h, hl, hc, hb⟩

theorem orthogonal_orthocrossing_drawing {V : Type} [DecidableEq V] {g : PeriodicGraph V}
    (valid : g.IsWellFormed) (locality : g.IsLocal) (degree : g.DegreeAtMost 4) :
    ∃ d : PeriodicGridDrawing, d.IsRealDrawing g ∧ d.IsRealLocal g ∧ d.IsRealOrthocrossing ∧
      d.IsOrthogonal ∧ d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d, h, hl, hc, ho, hb, _⟩ :=
    PeriodicOrthocrossing.GeneralPorts.local_orthogonal_orthocrossing_drawing valid locality degree
  exact ⟨d, h, hl, hc, ho, hb⟩

/-- Combine the unrestricted and local higher-dimensional SAT results. -/
theorem higher_dimensional_sat (d : Nat) (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (PeriodicConstraints.Satisfiable (Fin d → Int)) ∧
      LeanWang.CoREComplete (fun f : PeriodicCNFDimensions.Formula d =>
        (∀ c ∈ f, ∀ l ∈ c, ∀ r ∈ c, ∑ i, (l.1.2 i-r.1.2 i).natAbs ≤ 1) ∧
          PeriodicConstraints.Satisfiable (Fin d → Int) f) :=
  ⟨PeriodicCNFDimensions.satisfiable_coREComplete dimension, higher_local_sat d dimension⟩

/-- Combine quotient matching equivalence with the period-one witness. -/
theorem matching_period_one {L R : Type} [Fintype L] [Fintype R] {d : Nat}
    (es : List (PeriodicBipartite.Edge L R d)) :
    (PeriodicBipartite.HasPerfectMatching es ↔ PeriodicBipartite.HasQuotientMatching es) ∧
      (PeriodicBipartite.HasPerfectMatching es → PeriodicBipartite.HasPeriodOneMatching es) :=
  ⟨PeriodicBipartite.perfect_iff_quotient es, PeriodicBipartite.exists_period_one es⟩

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
export PeriodicThreeDM (localPlaneProblem_coREComplete localLineProblem_PSPACEComplete
  localPlanarLineProblem_PSPACEComplete)
export TrichromaticGraphOrientation (problem_coREComplete finiteProblem_npComplete)

theorem orientation_plane : LeanWang.CoREComplete TrichromaticGraphOrientation.LocalProblem :=
  TrichromaticGraphOrientation.localProblem_coREComplete

theorem orientation_line : Complexity.PSPACEComplete
    TrichromaticGraphOrientation.FlatEncoding.finEncoding
    TrichromaticGraphOrientation.LocalLineProblem :=
  TrichromaticGraphOrientation.localLineProblem_PSPACEComplete

end Native

namespace Data

/-! ## Periodic graphs in arbitrary dimension -/

/-- A lattice vector has d integer coordinates. A protoedge records its source,
target, and translation offset: its copy at z joins (source,z) to
(target,z+offset). Graphs retain lists of vertices and edge occurrences,
including isolated vertices, parallel edges, and both ends of loops. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Edge (V : Type) (d : ℕ) := V × V × Lattice d
abbrev Graph (V : Type) (d : ℕ) := List V × List (Edge V d)
def Edge.source {V : Type} {d : ℕ} (e : Edge V d) : V := e.1
def Edge.target {V : Type} {d : ℕ} (e : Edge V d) : V := e.2.1
def Edge.offset {V : Type} {d : ℕ} (e : Edge V d) : Lattice d := e.2.2
def Graph.vertices {V : Type} {d : ℕ} (g : Graph V d) : List V := g.1
def Graph.edges {V : Type} {d : ℕ} (g : Graph V d) : List (Edge V d) := g.2

def Adjacent {V : Type} {d : ℕ} (es : List (Edge V d))
    (u v : V × Lattice d) : Prop :=
  ∃ e ∈ es,
    (e.source = u.1 ∧ e.target = v.1 ∧ v.2 = u.2+e.offset) ∨
    (e.source = v.1 ∧ e.target = u.1 ∧ u.2 = v.2+e.offset)

/-- Well-formed graphs list distinct vertices and only listed edge endpoints.
Degree counts edge ends, twice for a loop. -/
def WellFormed {V : Type} {d : ℕ} (g : Graph V d) : Prop :=
  g.vertices.Nodup ∧ ∀ e ∈ g.edges, e.source ∈ g.vertices ∧ e.target ∈ g.vertices
def DegreeAtMost {V : Type} [DecidableEq V] {d : ℕ} (k : ℕ) (g : Graph V d) : Prop :=
  ∀ v, (g.edges.flatMap fun e => [e.source,e.target]).count v ≤ k

/-- Locality in the paper means L₁ offset length at most one, in every
dimension. Coordinate locality bounds each coordinate separately and also
allows diagonal offsets; it is a weaker hypothesis. -/
def Local {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ e ∈ es, ∑ i, (e.offset i).natAbs ≤ 1
def CoordinateLocal {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ e ∈ es, ∀ i, (e.offset i).natAbs ≤ 1

/-- Connectivity and proper two-colorings concern the entire infinite lift.
The vertex type supplies the protovertices, including isolated vertices. -/
def Connected {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ u v, Relation.ReflTransGen (Adjacent es) u v
def ProperColoring {V : Type} {d : ℕ} (es : List (Edge V d))
    (color : V × Lattice d → Bool) : Prop :=
  ∀ u v, Adjacent es u v → color u ≠ color v

theorem local_implies_coordinate_local {V : Type} {d : ℕ} (es : List (Edge V d))
    (h : Local es) : CoordinateLocal es := by
  intro e he i
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((e.offset j).natAbs))
    (Finset.mem_univ i)).trans (h e he)

/-- A general matching is a partially defined partner function: partners are
mutual, distinct, and adjacent. Period one means that this function commutes
with every lattice translation. A perfect matching may have any period. -/
def IsPartialMatching {V : Type} {d : ℕ} (es : List (Edge V d))
    (mate : V × Lattice d → Option (V × Lattice d)) : Prop :=
  (∀ u v, mate u = some v → mate v = some u ∧ Adjacent es u v) ∧
    ∀ u, mate u ≠ some u

def IsPeriodOne {V : Type} {d : ℕ}
    (mate : V × Lattice d → Option (V × Lattice d)) : Prop :=
  ∀ u t, mate (u.1,u.2+t) = (mate u).map (fun v => (v.1,v.2+t))

def HasPerfectMatching {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∃ mate : V × Lattice d → V × Lattice d,
    Function.Involutive mate ∧ (∀ u, mate u ≠ u) ∧ ∀ u, Adjacent es u (mate u)

/-- An augmenting path is a simple list with two free ends and an odd number
of edges. Consecutive edges alternate between unused and matched edges,
starting and ending with unused edges. -/
def IsAugmentingPath {V : Type} {d : ℕ} (es : List (Edge V d))
    (mate : V × Lattice d → Option (V × Lattice d)) (root : V × Lattice d)
    (path : List (V × Lattice d)) : Prop :=
  path.Nodup ∧ path.head? = some root ∧ mate root = none ∧
    (∀ last, path.getLast? = some last → mate last = none) ∧
    (∃ k, path.length = 2*k+2) ∧
    ∀ i (hi : i+1 < path.length), Adjacent es path[i] path[i+1] ∧
      (if i % 2 = 0 then mate path[i] ≠ some path[i+1]
       else mate path[i] = some path[i+1])

/-! ## Polygonal drawings of two-dimensional periodic graphs -/

/-- Drawing coordinates are integer pairs. For a graph in dimension two,
its offset vector has horizontal coordinate `offset 0` and vertical coordinate
`offset 1`. Only drawing notions specialize the graph dimension to two. -/
abbrev Cell := ℤ × ℤ

/-- Polygonal routes are lists of integer points interpreted as closed real
segments. A simple route has nonzero pieces; consecutive pieces meet only at
their common endpoint. The first and last pieces may close a loop. -/
abbrev Segment := Cell × Cell
def segments (route : List Cell) : List Segment := route.zip route.tail
def realPoint (c : Cell) : ℝ × ℝ := (c.1,c.2)
def SegmentContains (s : Segment) (p : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p.1 = s.1.1+t*(s.2.1-s.1.1) ∧
    p.2 = s.1.2+t*(s.2.2-s.1.2)
def SegmentInterior (s : Segment) (p : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p.1 = s.1.1+t*(s.2.1-s.1.1) ∧
    p.2 = s.1.2+t*(s.2.2-s.1.2)
def RouteContains (route : List Cell) (p : ℝ × ℝ) : Prop :=
  ∃ s ∈ segments route, SegmentContains s p
def RouteEndpoint (route : List Cell) (p : ℝ × ℝ) : Prop :=
  (∃ c, route.head? = some c ∧ p = realPoint c) ∨
    ∃ c, route.getLast? = some c ∧ p = realPoint c
def SimpleRoute (route : List Cell) : Prop :=
  2 ≤ route.length ∧ (∀ s ∈ segments route, s.1 ≠ s.2) ∧
    ∀ a ∈ (segments route).zipIdx, ∀ b ∈ (segments route).zipIdx,
      a.2 < b.2 → ∀ p : ℝ × ℝ, SegmentContains a.1 p → SegmentContains b.1 p →
        (a.2+1 = b.2 ∧ p = realPoint a.1.2) ∨
          (a.2 = 0 ∧ b.2+1 = (segments route).length ∧
            p = realPoint a.1.1 ∧ p = realPoint b.1.2)

def Horizontal (s : Segment) : Prop := s.1.2 = s.2.2 ∧ s.1.1 ≠ s.2.1
def Vertical (s : Segment) : Prop := s.1.1 = s.2.1 ∧ s.1.2 ≠ s.2.2

/-- A drawing stores M-1, vertex positions in vertex-list order, and routes
in edge-list order. Thus its square period M is positive by construction. -/
abbrev Drawing := ℕ × List Cell × List (List Cell)
def Drawing.gridSize (d : Drawing) : ℕ := d.1+1
def Drawing.vertexPositions (d : Drawing) : List Cell := d.2.1
def Drawing.edgeRoutes (d : Drawing) : List (List Cell) := d.2.2
def Drawing.edgeRoute (d : Drawing) (i : ℕ) : List Cell := d.edgeRoutes.getD i []
def Drawing.vertexPosition {V : Type} [DecidableEq V] (d : Drawing) (g : Graph V 2) (v : V) : Cell :=
  d.vertexPositions.getD (g.vertices.idxOf v) (0,0)
def scale (k : ℤ) (c : Cell) : Cell := (k*c.1,k*c.2)
def translatedRoute (d : Drawing) (i : ℕ) (z : Cell) : List Cell :=
  (d.edgeRoute i).map (fun c => ((d.gridSize : ℤ)*z.1+c.1, (d.gridSize : ℤ)*z.2+c.2))

/-- Compatibility matches the two finite lists, puts distinct vertex positions
strictly inside the fundamental square, and attaches each route to its source
and its offset-translated target. -/
def Compatible {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  WellFormed g ∧ d.vertexPositions.length = g.vertices.length ∧
    d.edgeRoutes.length = g.edges.length ∧ d.vertexPositions.Nodup ∧
    (∀ p ∈ d.vertexPositions, 0 < p.1 ∧ p.1 < d.gridSize ∧ 0 < p.2 ∧ p.2 < d.gridSize) ∧
    ∀ e ∈ g.edges.zipIdx,
      (d.edgeRoute e.2).head? = some (d.vertexPosition g e.1.source) ∧
      (d.edgeRoute e.2).getLast? = some
        ((d.vertexPosition g e.1.target).1+(d.gridSize : ℤ)*(e.1.offset 0),
         (d.vertexPosition g e.1.target).2+(d.gridSize : ℤ)*(e.1.offset 1))

def VerticesAvoidRoutes (d : Drawing) : Prop :=
  ∀ v ∈ d.vertexPositions, ∀ (vertexCell edgeCell : Cell) i, i < d.edgeRoutes.length →
    RouteContains (translatedRoute d i edgeCell)
      (realPoint (v.1+(d.gridSize : ℤ)*vertexCell.1, v.2+(d.gridSize : ℤ)*vertexCell.2)) →
    RouteEndpoint (translatedRoute d i edgeCell)
      (realPoint (v.1+(d.gridSize : ℤ)*vertexCell.1, v.2+(d.gridSize : ℤ)*vertexCell.2))
def RoutesMeetAtEndpoints (d : Drawing) : Prop :=
  ∀ i j a b, i < d.edgeRoutes.length → j < d.edgeRoutes.length → (i,a) ≠ (j,b) →
    ∀ p : ℝ × ℝ, RouteContains (translatedRoute d i a) p →
      RouteContains (translatedRoute d j b) p →
        RouteEndpoint (translatedRoute d i a) p ∧ RouteEndpoint (translatedRoute d j b) p

def IsDrawing {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  Compatible g d ∧ (∀ route ∈ d.edgeRoutes, SimpleRoute route) ∧ VerticesAvoidRoutes d
def PlanarDrawing {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  IsDrawing g d ∧ RoutesMeetAtEndpoints d
def Planar {V : Type} [DecidableEq V] (g : Graph V 2) : Prop := ∃ d : Drawing, PlanarDrawing g d

/-- Orthogonal routes have nondegenerate horizontal or vertical pieces.
Orthocrossing drawings allow further contacts only at perpendicular segment
interiors. Local drawings stay in the two closed cells of each edge's ends. -/
def Orthogonal (d : Drawing) : Prop :=
  ∀ route ∈ d.edgeRoutes, ∀ s ∈ segments route, Horizontal s ∨ Vertical s
def ProperCrossing (a b : Segment) (p : ℝ × ℝ) : Prop :=
  SegmentInterior a p ∧ SegmentInterior b p ∧
    ((Horizontal a ∧ Vertical b) ∨ (Vertical a ∧ Horizontal b))
def Orthocrossing (d : Drawing) : Prop :=
  ∀ i j a b, i < d.edgeRoutes.length → j < d.edgeRoutes.length → (i,a) ≠ (j,b) →
    ∀ p : ℝ × ℝ, RouteContains (translatedRoute d i a) p →
      RouteContains (translatedRoute d j b) p →
        (RouteEndpoint (translatedRoute d i a) p ∧ RouteEndpoint (translatedRoute d j b) p) ∨
        ∃ s ∈ segments (translatedRoute d i a), ∃ t ∈ segments (translatedRoute d j b),
          ProperCrossing s t p

def PointInCell (d : Drawing) (z : Cell) (p : ℝ × ℝ) : Prop :=
  (d.gridSize : ℝ)*z.1 ≤ p.1 ∧ p.1 ≤ (d.gridSize : ℝ)*(z.1+1) ∧
    (d.gridSize : ℝ)*z.2 ≤ p.2 ∧ p.2 ≤ (d.gridSize : ℝ)*(z.2+1)
def LocalDrawing {V : Type} (d : Drawing) (g : Graph V 2) : Prop :=
  ∀ e ∈ g.edges.zipIdx, ∀ p : ℝ × ℝ, RouteContains (d.edgeRoute e.2) p →
    PointInCell d (0,0) p ∨ PointInCell d (e.1.offset 0,e.1.offset 1) p

/-- A port identifies an indexed edge end: false is the source, true the target.
Degree-three vertices select one incident port. Directions are unit vectors;
(0,0) is the fallback for malformed or non-axis-aligned route ends. -/
abbrev Port (V : Type) := V × ℕ × Bool
def Port.vertex {V : Type} (p : Port V) : V := p.1
def Port.edgeIndex {V : Type} (p : Port V) : ℕ := p.2.1
def Port.isTarget {V : Type} (p : Port V) : Bool := p.2.2
def ports {V : Type} (g : Graph V 2) : List (Port V) :=
  g.edges.zipIdx.flatMap (fun e => [(e.1.source,e.2,false), (e.1.target,e.2,true)])
def portsAt {V : Type} [DecidableEq V] (g : Graph V 2) (v : V) : List (Port V) :=
  (ports g).filter (fun p => p.vertex = v)
def SelectedIncidences {V : Type} [DecidableEq V] (g : Graph V 2) (chosen : V → Port V) : Prop :=
  ∀ v ∈ g.vertices, (portsAt g v).length = 3 → chosen v ∈ portsAt g v

def direction (a b : Cell) : Cell :=
  if a.2 = b.2 then
    if a.1 < b.1 then (1,0) else if b.1 < a.1 then (-1,0) else (0,0)
  else if a.1 = b.1 then
    if a.2 < b.2 then (0,1) else if b.2 < a.2 then (0,-1) else (0,0)
  else (0,0)
def firstDirection : List Cell → Cell
  | a :: b :: _ => direction a b
  | _ => (0,0)
def portDirection {V : Type} (d : Drawing) (p : Port V) : Cell :=
  firstDirection (if p.isTarget then (d.edgeRoute p.edgeIndex).reverse else d.edgeRoute p.edgeIndex)
def IsNormalized {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (chosen : V → Port V) : Prop :=
  (∀ p ∈ ports g, (portsAt g p.vertex).length = 3 →
    portDirection d p ∈ [(-1,0),(0,1),(1,0)]) ∧
  ∀ v ∈ g.vertices, (portsAt g v).length = 3 → portDirection d (chosen v) = (-1,0)

end Data

namespace Correspondence

def edge (V : Type) : Data.Edge V 2 ≃ PeriodicEdge V where
  toFun e := ⟨e.1,e.2.1,finTwoArrowEquiv ℤ e.2.2⟩
  invFun e := (e.source,e.target,(finTwoArrowEquiv ℤ).symm e.offset)
  left_inv e := by
    rcases e with ⟨a,b,z⟩
    simp only [Equiv.symm_apply_apply]
  right_inv e := by cases e; rfl

def graph (V : Type) : Data.Graph V 2 ≃ PeriodicGraph V where
  toFun g := ⟨g.1,g.2.map (edge V)⟩
  invFun g := (g.vertices,g.edges.map (edge V).symm)
  left_inv g := by rcases g with ⟨vs,es⟩; simp
  right_inv g := by cases g; simp

def drawing : Data.Drawing ≃ PeriodicGridDrawing := PeriodicGridDrawing.equivData.symm

def segment (s : Data.Segment) : GridSegment := ⟨s.1,s.2⟩

@[simp] theorem segment_start (s : Data.Segment) : (segment s).start = s.1 := rfl
@[simp] theorem segment_finish (s : Data.Segment) : (segment s).finish = s.2 := rfl
@[simp] theorem segment_contains (s : Data.Segment) (p : ℝ × ℝ) :
    (segment s).RealContains p ↔ Data.SegmentContains s p := Iff.rfl
@[simp] theorem segment_interior (s : Data.Segment) (p : ℝ × ℝ) :
    (segment s).RealInteriorContains p ↔ Data.SegmentInterior s p := Iff.rfl
@[simp] theorem segment_horizontal (s : Data.Segment) :
    (segment s).IsHorizontal ↔ Data.Horizontal s := Iff.rfl
@[simp] theorem segment_vertical (s : Data.Segment) :
    (segment s).IsVertical ↔ Data.Vertical s := Iff.rfl

theorem segments (route : List Data.Cell) : gridPolylineSegments route = (Data.segments route).map segment := by
  induction route with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      change GridSegment.mk a b :: gridPolylineSegments (b::rest) =
        segment (a,b) :: (Data.segments (b::rest)).map segment
      rw [ih]
      rfl

theorem route_contains (route : List Data.Cell) (p : ℝ × ℝ) :
    GridPolyline.RealContains route p ↔ Data.RouteContains route p := by
  simp [GridPolyline.RealContains, segments, Data.RouteContains]

theorem route_endpoint (route : List Data.Cell) (p : ℝ × ℝ) :
    GridPolyline.RealIsEndpoint route p ↔ Data.RouteEndpoint route p := Iff.rfl

theorem simple_route (route : List Data.Cell) :
    GridPolyline.IsRealSimple route ↔ Data.SimpleRoute route := by
  simp only [GridPolyline.IsRealSimple, Data.SimpleRoute, segments, List.length_map,
    List.zipIdx_map, List.forall_mem_map, segment_start, segment_finish]
  rfl

@[simp] theorem drawing_positions (d : Data.Drawing) : (drawing d).vertexPositions = d.2.1 := rfl
@[simp] theorem drawing_routes (d : Data.Drawing) : (drawing d).edgeRoutes = d.2.2 := rfl
@[simp] theorem drawing_period (d : Data.Drawing) : (drawing d).gridSize = Data.Drawing.gridSize d := rfl
@[simp] theorem drawing_route (d : Data.Drawing) (i : ℕ) :
    (drawing d).edgeRoute i = Data.Drawing.edgeRoute d i := rfl
@[simp] theorem drawing_translate (d : Data.Drawing) (i : ℕ) (z : Data.Cell) :
    (drawing d).realEdgeRoute i z = Data.translatedRoute d i z := rfl

@[simp] theorem graph_vertices {V : Type} (g : Data.Graph V 2) : (graph V g).vertices = g.1 := rfl
@[simp] theorem graph_edges {V : Type} (g : Data.Graph V 2) : (graph V g).edges = g.2.map (edge V) := rfl
@[simp] theorem edge_source {V : Type} (e : Data.Edge V 2) : (edge V e).source = e.1 := rfl
@[simp] theorem edge_target {V : Type} (e : Data.Edge V 2) : (edge V e).target = e.2.1 := rfl
@[simp] theorem edge_offset {V : Type} (e : Data.Edge V 2) : (edge V e).offset = (e.2.2 0,e.2.2 1) := rfl

theorem wellFormed {V : Type} [DecidableEq V] (g : Data.Graph V 2) :
    (graph V g).IsWellFormed ↔ Data.WellFormed g := by
  simp only [PeriodicGraph.IsWellFormed, Data.WellFormed, graph_vertices, graph_edges,
    List.forall_mem_map, edge_source, edge_target]
  rfl

theorem locality {V : Type} (g : Data.Graph V 2) : (graph V g).IsLocal ↔ Data.Local g.edges := by
  simp only [PeriodicGraph.IsLocal, Data.Local, graph_edges, List.forall_mem_map,
    PeriodicEdge.span, edge_offset, Fin.sum_univ_two]
  rfl

theorem degree {V : Type} [DecidableEq V] (k : ℕ) (g : Data.Graph V 2) :
    (graph V g).DegreeAtMost k ↔ Data.DegreeAtMost k g := by
  simp [PeriodicGraph.DegreeAtMost, PeriodicGraph.incidences, Data.DegreeAtMost,
    Data.Graph.edges, Data.Edge.source, Data.Edge.target, List.flatMap_map, PeriodicEdge.incidences]

theorem compatible {V : Type} [DecidableEq V] (g : Data.Graph V 2) (d : Data.Drawing) :
    (drawing d).IsCompatible (graph V g) ↔ Data.Compatible g d := by
  simp only [PeriodicGridDrawing.IsCompatible, Data.Compatible, wellFormed,
    drawing_positions, drawing_routes, graph_vertices, graph_edges, List.length_map,
    PeriodicGridDrawing.PositionInFundamentalSquare, PeriodicGridDrawing.RoutesMatch,
    List.zipIdx_map, List.forall_mem_map, Prod.map_fst, Prod.map_snd,
    edge_source, edge_target, edge_offset, drawing_route,
    PeriodicGridDrawing.vertexPosition, PeriodicGridDrawing.periodTranslation,
    drawing_period, Cell.add, Cell.scale]
  rfl

theorem vertices_avoid (d : Data.Drawing) :
    (drawing d).RealVerticesAvoidRoutes ↔ Data.VerticesAvoidRoutes d := by
  simp only [PeriodicGridDrawing.RealVerticesAvoidRoutes, Data.VerticesAvoidRoutes,
    drawing_positions, drawing_routes, drawing_translate, route_contains, route_endpoint]
  rfl

theorem routes_meet (d : Data.Drawing) :
    (drawing d).RealRoutesMeetOnlyAtEndpoints ↔ Data.RoutesMeetAtEndpoints d := by
  simp only [PeriodicGridDrawing.RealRoutesMeetOnlyAtEndpoints, Data.RoutesMeetAtEndpoints,
    drawing_routes, drawing_translate, route_contains, route_endpoint]
  rfl

theorem isDrawing {V : Type} [DecidableEq V] (g : Data.Graph V 2) (d : Data.Drawing) :
    (drawing d).IsRealDrawing (graph V g) ↔ Data.IsDrawing g d := by
  simp only [PeriodicGridDrawing.IsRealDrawing, Data.IsDrawing, compatible,
    PeriodicGridDrawing.RealRoutesAreSimple, drawing_routes, simple_route, vertices_avoid]
  rfl

theorem planar {V : Type} [DecidableEq V] (g : Data.Graph V 2) (d : Data.Drawing) :
    (drawing d).IsRealPlanarDrawing (graph V g) ↔ Data.PlanarDrawing g d :=
  and_congr (isDrawing g d) (routes_meet d)

theorem localDrawing {V : Type} (g : Data.Graph V 2) (d : Data.Drawing) :
    (drawing d).IsRealLocal (graph V g) ↔ Data.LocalDrawing d g := by
  simp only [PeriodicGridDrawing.IsRealLocal, Data.LocalDrawing, graph_edges, List.zipIdx_map,
    List.forall_mem_map, drawing_route, route_contains,
    PeriodicGridDrawing.RealPointInCell, Data.PointInCell, drawing_period]
  rfl

theorem orthocrossing (d : Data.Drawing) :
    (drawing d).IsRealOrthocrossing ↔ Data.Orthocrossing d := by
  simp [PeriodicGridDrawing.IsRealOrthocrossing, Data.Orthocrossing, drawing_routes,
    drawing_translate, route_contains, route_endpoint, segments,
    PeriodicGridDrawing.RealProperlyCrossesAt, Data.ProperCrossing,
    segment_interior, segment_horizontal, segment_vertical, Data.Drawing.edgeRoutes]

theorem orthogonal (d : Data.Drawing) :
    (drawing d).IsOrthogonal ↔ Data.Orthogonal d := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  simp only [drawing_routes, PeriodicOrthocrossing.orthogonalPolyline_iff_segments, Data.Orthogonal,
    segments, List.forall_mem_map, GridSegment.IsAxisAligned, segment_horizontal, segment_vertical]
  rfl


open PeriodicOrthocrossing

def port (V : Type) : Data.Port V ≃ GraphPort V where
  toFun p := ⟨p.1,p.2.1,if p.2.2 then .target else .source⟩
  invFun p := (p.vertex,p.edgeIndex,match p.endKind with | .source => false | .target => true)
  left_inv p := by rcases p with ⟨v,i,b⟩; cases b <;> rfl
  right_inv p := by rcases p with ⟨v,i,b⟩; cases b <;> rfl

@[simp] theorem port_vertex {V : Type} (p : Data.Port V) :
    (port V p).vertex = Data.Port.vertex p := rfl

theorem ports {V : Type} (g : Data.Graph V 2) :
    allPorts (graph V g) = (Data.ports g).map (port V) := by
  simp only [allPorts, Data.ports, graph_edges, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap]
  congr 1

theorem portsAt {V : Type} [DecidableEq V] (g : Data.Graph V 2) (v : V) :
    PeriodicOrthocrossing.portsAt (graph V g) v = (Data.portsAt g v).map (port V) := by
  simp [PeriodicOrthocrossing.portsAt, Data.portsAt, ports, List.filter_map, Function.comp_def]

theorem selection {V : Type} [DecidableEq V] (g : Data.Graph V 2) (chosen : V → Data.Port V) :
    GeneralVertexNormalization.SelectedIncidences (graph V g) (fun v => port V (chosen v)) ↔
      Data.SelectedIncidences g chosen := by
  simp only [GeneralVertexNormalization.SelectedIncidences, Data.SelectedIncidences,
    graph_vertices, portsAt, List.length_map, List.mem_map, (port V).injective.eq_iff, exists_eq_right]
  rfl

theorem direction (a b : Data.Cell) : (AxisDirection.between a b).step = Data.direction a b := by
  unfold AxisDirection.between Data.direction
  split_ifs <;> rfl

theorem firstDirection (route : List Data.Cell) :
    (AxisDirection.polylineFirstDirection route).step = Data.firstDirection route := by
  cases route with
  | nil => rfl
  | cons a rest => cases rest with
    | nil => rfl
    | cons b rest => exact direction a b

theorem portDirection {V : Type} (d : Data.Drawing) (p : Data.Port V) :
    (GeneralVertexNormalization.portDirection (drawing d) (port V p)).step = Data.portDirection d p := by
  rcases p with ⟨v,i,b⟩
  cases b
  · exact firstDirection _
  · change ((AxisDirection.polylineFirstDirection _).opposite.opposite).step = _
    have involution (a : AxisDirection) : a.opposite.opposite = a := by cases a <;> rfl
    rw [involution]
    exact firstDirection _

theorem step_west (a : AxisDirection) : a = .west ↔ a.step = (-1,0) := by
  cases a <;> decide

theorem step_three (a : AxisDirection) :
    (a = .west ∨ a = .north ∨ a = .east) ↔ a.step ∈ [(-1,0),(0,1),(1,0)] := by
  cases a <;> decide

theorem normalized {V : Type} [DecidableEq V] (g : Data.Graph V 2) (d : Data.Drawing)
    (chosen : V → Data.Port V) :
    GeneralVertexNormalization.IsNormalized (graph V g) (drawing d) (fun v => port V (chosen v)) ↔
      Data.IsNormalized g d chosen := by
  simp only [GeneralVertexNormalization.IsNormalized, Data.IsNormalized, ports,
    List.forall_mem_map, portsAt, List.length_map, graph_vertices, port_vertex,
    ]
  simp only [step_three]
  simp only [step_west, portDirection]
  rfl

end Correspondence

namespace Data

open Correspondence

theorem orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V 2)
    (valid : WellFormed g) (hl : Local g.edges) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d,h⟩ := Native.orthocrossing_drawing ((wellFormed g).mpr valid) ((locality g).mpr hl)
  refine ⟨drawing.symm d, ?_⟩
  rw [← drawing.apply_symm_apply d] at h
  simpa only [isDrawing, localDrawing, orthocrossing, drawing_period,
    graph_vertices, graph_edges, List.length_map, Graph.vertices, Graph.edges] using h

theorem orthogonal_orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V 2)
    (valid : WellFormed g) (hl : Local g.edges) (hd : DegreeAtMost 4 g) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      Orthogonal d ∧ d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d,h⟩ := Native.orthogonal_orthocrossing_drawing
    ((wellFormed g).mpr valid) ((locality g).mpr hl) ((degree 4 g).mpr hd)
  refine ⟨drawing.symm d, ?_⟩
  rw [← drawing.apply_symm_apply d] at h
  simpa only [isDrawing, localDrawing, orthocrossing, orthogonal, drawing_period,
    graph_vertices, graph_edges, List.length_map, Graph.vertices, Graph.edges] using h

theorem orthogonal_refinement {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (hp : PlanarDrawing g d) (hd : DegreeAtMost 4 g) (hl : Local g.edges) (hr : LocalDrawing d g) :
    ∃ out : Drawing, PlanarDrawing g out ∧ LocalDrawing out g ∧ Orthogonal out ∧
      out.gridSize ≤ 84480*d.gridSize^3 ∧
      out.vertexPositions = d.vertexPositions.map
        (fun p => ((((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.1,
          (((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.2)) := by
  obtain ⟨out,h⟩ := Native.polygonal_cubic_refinement ((planar g d).mpr hp)
    ((degree 4 g).mpr hd) ((locality g).mpr hl) ((localDrawing g d).mpr hr)
  refine ⟨drawing.symm out, ?_⟩
  rw [← drawing.apply_symm_apply out] at h
  simp only [planar, localDrawing, orthogonal, drawing_period, drawing_positions, Drawing.vertexPositions,
    PeriodicGridDrawing.RawBendSubdivision.cubicFactor,
    OrthogonalDrawingRefinement.Cubic.rasterFactor,
    OrthogonalDrawingRefinement.Cubic.coreFactor] at h ⊢
  convert h using 1; rfl

theorem normalize_incidence_directions {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (hp : PlanarDrawing g d) (ho : Orthogonal d)
    (chosen : V → Port V) (hs : SelectedIncidences g chosen) :
    ∃ out : Drawing, PlanarDrawing g out ∧ Orthogonal out ∧
      IsNormalized g out chosen ∧ out.gridSize = 32*d.gridSize ∧
      out.vertexPositions = d.vertexPositions.map (scale 32) ∧
      (LocalDrawing d g → LocalDrawing out g) := by
  obtain ⟨out,h⟩ := Native.lemma23 ((planar g d).mpr hp) ((orthogonal d).mpr ho)
    (fun v => port V (chosen v)) ((selection g chosen).mpr hs)
  refine ⟨drawing.symm out, ?_⟩
  rw [← drawing.apply_symm_apply out] at h
  simp only [planar, orthogonal, normalized, drawing_period, drawing_positions,
    localDrawing, Drawing.vertexPositions] at h ⊢
  convert h using 1; rfl

end Data


namespace Data

abbrev Literal := PeriodicLiteral ℕ

abbrev Formula := PeriodicCNF ℕ

def Satisfies (f : Formula) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) c, c ∈ f.clauses → ∃ l ∈ c,
    a l.atom (z.1+l.offset.1, z.2+l.offset.2) = l.value

def Satisfiable (f : Formula) : Prop := ∃ a, Satisfies f a

def LocalFormula (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, ∀ r ∈ c,
    (l.offset.1-r.offset.1).natAbs + (l.offset.2-r.offset.2).natAbs ≤ 1

def WidthAtMost (k : ℕ) (f : Formula) : Prop := ∀ c ∈ f.clauses, c.length ≤ k

def OccurrencesAtMost (k : ℕ) (f : Formula) : Prop :=
  ∀ v, (f.clauses.flatMap fun c => c.map PeriodicLiteral.atom).count v ≤ k

def ZeroDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset = (0,0)

def OneDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset.2 = 0

def LineSAT (f : Formula) : Prop :=
  (∃ a : ℕ → ℤ → Bool, ∀ (z : ℤ) c, c ∈ f.clauses →
    ∃ l ∈ c, a l.atom (z+l.offset.1) = l.value) ∧ OneDimensional f ∧ f.IsLocalOnLine

abbrev formulaEncoding := PeriodicCNFFlatEncoding.finEncoding

def ExactlyOneSatisfiable (f : Formula) : Prop :=
  ∃ a : ℕ → Cell → Bool, ∀ (z : Cell) c, c ∈ f.clauses →
    (c.map fun l => a l.atom (z.1+l.offset.1, z.2+l.offset.2) == l.value).count true = 1


abbrev FormulaIn (d : ℕ) := List (List ((ℕ × Lattice d) × Bool))

def SatisfiableIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∃ a : ℕ → Lattice d → Bool, ∀ z c, c ∈ f → ∃ l ∈ c, a l.1.1 (z+l.1.2) = l.2

def LocalIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∀ c ∈ f, ∀ l ∈ c, ∀ r ∈ c, ∑ i, (l.1.2 i-r.1.2 i).natAbs ≤ 1

abbrev PlanarInput := PeriodicPlanarSAT.Input ℕ

abbrev planarEncoding := PeriodicPlanarSAT.FlatEncoding.finEncoding

def PlanarSAT (i : PlanarInput) : Prop :=
  Satisfiable i.1 ∧ PeriodicPlanarSAT.GridBound 8847360 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.OrbitCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar

def PlanarExactOne (i : PlanarInput) : Prop :=
  ExactlyOneSatisfiable i.1 ∧ PeriodicPlanarSAT.GridBound 637009920 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.FiniteCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar

def PlanarLineSAT (i : PlanarInput) : Prop :=
  PlanarSAT i ∧ OneDimensional i.1

def PlanarLineExactOne (i : PlanarInput) : Prop :=
  PlanarExactOne i ∧ OneDimensional i.1

abbrev PeriodicThreeDMInput := PeriodicThreeDM.NormalizationCompiler.Input

def Matches (p : PeriodicThreeDM) : Prop :=
  ∃ selected : ℕ → Cell → Bool, ∀ color atom, atom < p.elementCount color → ∀ (z : Cell),
    ((p.incidences color atom).map fun i =>
      selected i.tripleIndex (z.1-i.offset.1, z.2-i.offset.2)).count true = 1

def ThreeDMPlane (i : PeriodicThreeDMInput) : Prop :=
  Matches i.problem ∧ i.problem.IsLocal ∧ i.problem.IsWellFormed ∧
    i.problem.DegreeTwoOrThree ∧
    PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true

def ThreeDMLine (p : PeriodicThreeDM) : Prop :=
  Matches p ∧ p.IsWellFormed ∧ p.DegreeTwoOrThree ∧ p.IsOneDimensional ∧ p.IsLocal

abbrev OrientationInput := TrichromaticGraphOrientation.Input

def IsOrientation (i : OrientationInput) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) v, v < i.1.length → if i.1.getD v false then
    (∀ l ∈ TrichromaticGraphOrientation.incoming i v,
      ∀ r ∈ TrichromaticGraphOrientation.incoming i v,
      (a l.atom (z.1+l.offset.1,z.2+l.offset.2) = l.value) ↔
        (a r.atom (z.1+r.offset.1,z.2+r.offset.2) = r.value))
  else ((TrichromaticGraphOrientation.incoming i v).map fun l =>
    a l.atom (z.1+l.offset.1,z.2+l.offset.2) == l.value).count true = 1

def Orientable (i : OrientationInput) : Prop := ∃ a, IsOrientation i a

def OrientationProblem (i : OrientationInput) : Prop :=
  Orientable i ∧ TrichromaticGraphOrientation.IsWellFormed i

def OrientationLocal (i : OrientationInput) : Prop :=
  OrientationProblem i ∧ ∀ e ∈ i.2, e.1.offset.1.natAbs+e.1.offset.2.natAbs ≤ 1

def OrientationLine (i : OrientationInput) : Prop :=
  OrientationLocal i ∧ ∀ e ∈ i.2, e.1.offset.2 = 0

def OrientationFinite (i : OrientationInput) : Prop :=
  (∃ a : ℕ → Bool, IsOrientation i (fun e _ => a e)) ∧
    TrichromaticGraphOrientation.IsWellFormed i ∧ ∀ e ∈ i.2, e.1.offset = (0,0)

abbrev HornRule := Horn.PeriodicRule

abbrev HornSatisfiable := @Horn.PeriodicSatisfiable

abbrev BipartiteEdge := PeriodicBipartite.Edge

def PerfectMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d), ∀ u, ∃ e ∈ es,
    e.left = u.1 ∧ e.right = (f u).1 ∧ (f u).2 = u.2+e.offset

def PeriodOneMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, ∃ e ∈ es, e.left = u.1 ∧ e.right = (f u).1 ∧ (f u).2 = u.2+e.offset) ∧
    ∀ l z t, f (l,z+t) = ((f (l,z)).1, (f (l,z)).2+t)

def QuotientMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : L ≃ R, ∀ l, ∃ e ∈ es, e.left = l ∧ e.right = f l

macro "graph_abstract_logic" : tactic => `(tactic| (
  dsimp only [Satisfies, Satisfiable, LocalFormula, WidthAtMost, OccurrencesAtMost, ZeroDimensional, OneDimensional, LineSAT, ExactlyOneSatisfiable, SatisfiableIn, LocalIn, PlanarSAT, PlanarExactOne, PlanarLineSAT, PlanarLineExactOne, Matches, ThreeDMPlane, ThreeDMLine, IsOrientation, Orientable, OrientationProblem, OrientationLocal, OrientationLine, OrientationFinite, HornSatisfiable, PerfectMatching, PeriodOneMatching, QuotientMatching]
  dsimp only [PeriodicCNF.LocalPeriodicCNF1DSAT, PeriodicCNF.LocalPeriodicThreeCNF1DSAT,
    PeriodicCNF.LocalPeriodicThreeSATThree1DSAT, PeriodicCNF.IsOneDimensional,
    PeriodicCNF.SatisfiableOnLine, PeriodicCNF.SatisfiesOnLine,
    PeriodicCNF.WidthAtMost, PeriodicCNF.OccurrencesAtMost,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSAT,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree, PeriodicExactOneCNF.LocalOneDimensionalSAT,
    PeriodicCNF.IsLocal, PeriodicCNF.Satisfiable, PeriodicCNF.Satisfies, PeriodicLiteral.Holds,
    PeriodicOneInThree.Satisfiable, PeriodicOneInThree.Satisfies, PeriodicOneInThree.ClauseHolds,
    PeriodicPlanarSAT.Orbit.BoundedLocalProblem, PeriodicPlanarSAT.Orbit.BoundedLocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.LocalProblem, PeriodicPlanarSAT.Orbit.LocalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.Problem, PeriodicPlanarSAT.Orbit.ThreeOccurrenceProblem,
    PeriodicPlanarSAT.Orbit.Valid, PeriodicPlanarSAT.Orbit.LocalOneDimensionalProblem,
    PeriodicPlanarSAT.Orbit.LocalOneDimensionalThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.ExactOneProblem, PeriodicPlanarSAT.Unbounded.ExactOneThreeOccurrenceProblem,
    PeriodicPlanarSAT.Unbounded.Valid, PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneProblem,
    PeriodicPlanarSAT.Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,
    PeriodicThreeDM.LocalPlaneProblem, PeriodicThreeDM.PlaneProblem,
    PeriodicThreeDM.LocalLineProblem, PeriodicThreeDM.LocalPlanarLineProblem,
    PeriodicThreeDM.Satisfiable, PeriodicThreeDM.Satisfies,
    TrichromaticGraphOrientation.LocalProblem, TrichromaticGraphOrientation.LocalLineProblem,
    TrichromaticGraphOrientation.Problem, TrichromaticGraphOrientation.FiniteProblem,
    TrichromaticGraphOrientation.FiniteHasOrientation, TrichromaticGraphOrientation.FiniteIsOrientation,
    TrichromaticGraphOrientation.HasOrientation, TrichromaticGraphOrientation.IsOrientation,
    TrichromaticGraphOrientation.Coherent, TrichromaticGraphOrientation.IsLocal,
    TrichromaticGraphOrientation.IsOneDimensional, TrichromaticGraphOrientation.ZeroOffsets,
    Cell.add, Cell.sub]
  tauto
))

theorem line_sat : ComplexityAbstract.PSPACEComplete formulaEncoding.encode LineSAT := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff formulaEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localPeriodicCNF1DSAT_PSPACEComplete)
  graph_abstract_logic

theorem line_three_sat : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => LineSAT f ∧ WidthAtMost 3 f) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff formulaEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localPeriodicThreeCNF1DSAT_PSPACEComplete)
  graph_abstract_logic

theorem line_three_sat_three : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => LineSAT f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff formulaEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localPeriodicThreeSATThree1DSAT_PSPACEComplete)
  graph_abstract_logic

theorem plane_three_sat : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f) := by
  apply Native.coRE_congr (fun x => ?_) (Native.plane_three_sat)
  graph_abstract_logic

theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) := by
  apply Native.coRE_congr (fun x => ?_) (Native.plane_three_sat_three)
  graph_abstract_logic

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f => ExactlyOneSatisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) := by
  apply Native.coRE_congr (fun x => ?_) (Native.plane_exact_one)
  graph_abstract_logic

theorem line_exact_one : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧ WidthAtMost 3 f) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff formulaEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localOneDimensionalThreeSAT_PSPACEComplete)
  graph_abstract_logic

theorem line_exact_one_three : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧
      WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff formulaEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localOneDimensionalThreeSATThree_PSPACEComplete)
  graph_abstract_logic

theorem higher_dimensional_sat (d : ℕ) (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (@SatisfiableIn d) ∧
      LeanWang.CoREComplete (fun f : FormulaIn d => SatisfiableIn f ∧ LocalIn f) := by
  obtain ⟨plain,loc⟩ := Native.higher_dimensional_sat d dimension
  refine ⟨plain, Native.coRE_congr (fun f => ?_) loc⟩
  change (LocalIn f ∧ SatisfiableIn f) ↔ (SatisfiableIn f ∧ LocalIn f)
  tauto

theorem cook_levin : ComplexityAbstract.NPHard formulaEncoding.encode
    (fun f => Satisfiable f ∧ ZeroDimensional f ∧ WidthAtMost 3 f) := by
  apply (ComplexityAbstractBridge.npHard_iff formulaEncoding _).mpr
  have eq : (fun f : Formula => FiniteCNF.ZeroOffsets f ∧ PeriodicCNF.WidthAtMost 3 f ∧ PeriodicCNF.Satisfiable f) =
      (fun f => Satisfiable f ∧ ZeroDimensional f ∧ WidthAtMost 3 f) := by
    funext f
    apply propext
    change (ZeroDimensional f ∧ WidthAtMost 3 f ∧ Satisfiable f) ↔ _
    tauto
  rw [← eq]
  intro A encoding language member
  exact Native.zero_dimensional_sat encoding language member

theorem planar_plane_sat : LeanWang.CoREComplete PlanarSAT := by
  apply Native.coRE_congr (fun x => ?_) (Native.planar_plane_sat)
  graph_abstract_logic

theorem planar_plane_three_occurrences : LeanWang.CoREComplete
    (fun i => PlanarSAT i ∧ OccurrencesAtMost 3 i.1) := by
  apply Native.coRE_congr (fun x => ?_) (Native.planar_plane_three_sat)
  graph_abstract_logic

theorem planar_plane_exact_one : LeanWang.CoREComplete PlanarExactOne := by
  apply Native.coRE_congr (fun x => ?_) (Native.planar_plane_exact_one)
  graph_abstract_logic

theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i => PlanarExactOne i ∧ OccurrencesAtMost 3 i.1) := by
  apply Native.coRE_congr (fun x => ?_) (Native.planar_plane_exact_one_three)
  graph_abstract_logic

theorem planar_line_sat : ComplexityAbstract.PSPACEComplete planarEncoding.encode PlanarLineSAT := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff planarEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.ordinary_PSPACEComplete)
  graph_abstract_logic

theorem planar_line_three_occurrences : ComplexityAbstract.PSPACEComplete planarEncoding.encode
    (fun i => PlanarLineSAT i ∧ OccurrencesAtMost 3 i.1) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff planarEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.planar_line_three_sat)
  graph_abstract_logic

theorem planar_line_exact_one : ComplexityAbstract.PSPACEComplete planarEncoding.encode PlanarLineExactOne := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff planarEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.exactOne_PSPACEComplete)
  graph_abstract_logic

theorem planar_line_exact_one_three : ComplexityAbstract.PSPACEComplete planarEncoding.encode
    (fun i => PlanarLineExactOne i ∧ OccurrencesAtMost 3 i.1) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff planarEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.planar_line_exact_one_three)
  graph_abstract_logic

theorem three_dm_plane : LeanWang.CoREComplete ThreeDMPlane := by
  apply Native.coRE_congr (fun x => ?_) (Native.localPlaneProblem_coREComplete)
  graph_abstract_logic

theorem three_dm_line : ComplexityAbstract.PSPACEComplete PeriodicThreeDM.FlatEncoding.finEncoding.encode
    ThreeDMLine := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff PeriodicThreeDM.FlatEncoding.finEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localLineProblem_PSPACEComplete)
  graph_abstract_logic

theorem three_dm_planar_line : ComplexityAbstract.PSPACEComplete PeriodicThreeDM.FlatEncoding.Planar.finEncoding.encode
    (fun i => ThreeDMLine i.problem ∧
      PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true) := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff PeriodicThreeDM.FlatEncoding.Planar.finEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.localPlanarLineProblem_PSPACEComplete)
  graph_abstract_logic

theorem orientation_plane : LeanWang.CoREComplete OrientationLocal := by
  apply Native.coRE_congr (fun x => ?_) (Native.orientation_plane)
  graph_abstract_logic

theorem orientation_line : ComplexityAbstract.PSPACEComplete TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode
    OrientationLine := by
  apply (ComplexityAbstractBridge.pspaceComplete_iff TrichromaticGraphOrientation.FlatEncoding.finEncoding _).mpr
  apply Native.pspace_congr (fun x => ?_) (Native.orientation_line)
  graph_abstract_logic

theorem orientation_finite : ComplexityAbstract.NPComplete TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode
    OrientationFinite := by
  apply (ComplexityAbstractBridge.npComplete_iff TrichromaticGraphOrientation.FlatEncoding.finEncoding _).mpr
  apply Native.np_congr (fun x => ?_) (Native.finiteProblem_npComplete)
  graph_abstract_logic

theorem horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule V G))
    (h : HornSatisfiable rules) :
    ∃ a : V → Prop, Horn.PeriodicSatisfies rules (fun v _ => a v) := Native.exists_period_one rules h

theorem dual_horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule V G))
    (h : Horn.PeriodicDualSatisfiable rules) :
    ∃ a : V → Prop, Horn.PeriodicDualSatisfies rules (fun v _ => a v) := Native.dual_exists_period_one rules h

theorem horn_linear {n : ℕ} {G : Type} [AddGroup G]
    (rules : Array (HornRule (Fin n) G)) :
    (Horn.PeriodicIndexed.check rules = true ↔ HornSatisfiable rules.toList) ∧
    (Horn.PeriodicIndexed.check rules = true ↔ Horn.PeriodicDualSatisfiable rules.toList) ∧
    Horn.PeriodicIndexed.totalCost rules ≤ 72*Horn.PeriodicIndexed.inputSize rules := Native.certified rules

theorem two_sat_polynomial {n d : ℕ} (f : PeriodicTwoSAT.Formula (Fin n) d)
    (locality : PeriodicTwoSAT.LocalDifferences f) :
    ((PeriodicTwoSAT.solveLocal f).1 = true ↔ PeriodicTwoSAT.Satisfiable f) ∧
      (PeriodicTwoSAT.solveLocal f).2 ≤
        PeriodicTwoSAT.localCoefficient d*(PeriodicTwoSAT.inputSize f)^(PeriodicTwoSAT.degree d) := Native.local_certified f locality

theorem matching_period_one {L R : Type} [Fintype L] [Fintype R] {d : ℕ}
    (es : List (BipartiteEdge L R d)) :
    (PerfectMatching es ↔ QuotientMatching es) ∧
      (PerfectMatching es → PeriodOneMatching es) := Native.matching_period_one es

theorem matching_algorithm {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d)) :
    ((PeriodicBipartite.matchingSolver es).table.isSome = true ↔ PerfectMatching es) ∧
    PeriodicBipartite.MatchingResultSpec es (PeriodicBipartite.matchingSolver es).table ∧
    (PeriodicBipartite.matchingSolver es).cost ≤ 1000*(es.length+1)*(Nat.sqrt (n+m)+1) := Native.matchingSolver_certified es

theorem matching_nonempty_cost {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d))
    (nonempty : 0 < es.length) :
    (PeriodicBipartite.matchingSolver es).cost ≤ 4000*es.length*Nat.sqrt (n+m) := Native.matchingSolver_edge_sqrt_bound es nonempty

theorem short_augmenting_path {L R : Type} [DecidableEq L] [DecidableEq R]
    [Fintype L] [Fintype R] {d : ℕ} (es : List (BipartiteEdge L R d))
    (perfect : PerfectMatching es) (matching : PeriodicBipartite.PeriodOnePartial es) :
    PeriodicBipartite.PerfectPartial matching ∨ Nonempty (PeriodicBipartite.ShortAugmentingPath matching) := Native.perfect_or_short_augmenting es perfect matching

end Data


namespace Correspondence

def arc (V : Type) (d : ℕ) : Data.Edge V d ≃ PeriodicLatticeGraph.Arc V d where
  toFun e := ⟨e.1,e.2.1,e.2.2⟩
  invFun e := (e.source,e.target,e.offset)
  left_inv e := by rcases e with ⟨a,b,z⟩; rfl
  right_inv e := by cases e; rfl

theorem arcs_adj {V : Type} {d : ℕ} (es : List (Data.Edge V d)) (u v : V × Data.Lattice d) :
    PeriodicLatticeGraph.UndirectedAdj (es.map (arc V d)) u v ↔ Data.Adjacent es u v := by
  constructor
  · rintro (⟨e,he,hs,ht,hz⟩ | ⟨e,he,hs,ht,hz⟩)
    · obtain ⟨orig,mem,rfl⟩ := List.mem_map.mp he
      exact ⟨orig,mem,Or.inl ⟨hs,ht,hz⟩⟩
    · obtain ⟨orig,mem,rfl⟩ := List.mem_map.mp he
      exact ⟨orig,mem,Or.inr ⟨hs,ht,hz⟩⟩
  · rintro ⟨e,he,(⟨hs,ht,hz⟩ | ⟨hs,ht,hz⟩)⟩
    · exact Or.inl ⟨arc V d e,List.mem_map.mpr ⟨e,he,rfl⟩,hs,ht,hz⟩
    · exact Or.inr ⟨arc V d e,List.mem_map.mpr ⟨e,he,rfl⟩,hs,ht,hz⟩

theorem arcs_connected {V : Type} {d : ℕ} (es : List (Data.Edge V d)) :
    PeriodicLatticeGraph.Connected (es.map (arc V d)) ↔ Data.Connected es := by
  constructor
  · intro h u v
    exact Relation.ReflTransGen.mono (fun _ _ h => (arcs_adj es _ _).mp h) u v (h u v)
  · intro h u v
    exact Relation.ReflTransGen.mono (fun _ _ h => (arcs_adj es _ _).mpr h) u v (h u v)

theorem arcs_coloring {V : Type} {d : ℕ} (es : List (Data.Edge V d))
    (color : V × Data.Lattice d → Bool) :
    PeriodicLatticeGraph.ProperColoring (es.map (arc V d)) color ↔ Data.ProperColoring es color := by
  constructor
  · intro h u v huv
    exact h u v ((arcs_adj es u v).mpr huv)
  · intro h u v huv
    exact h u v ((arcs_adj es u v).mp huv)

end Correspondence

namespace Data

theorem bipartition_doubled {V : Type} {d : ℕ}
    (es : List (Edge V d)) (connected : Connected es)
    (color : V × Lattice d → Bool) (proper : ProperColoring es color)
    (v : V) (z t : Lattice d) : color (v, z+(t+t)) = color (v,z) :=
  Native.bipartition_two_periodic (es.map (Correspondence.arc V d))
    ((Correspondence.arcs_connected es).mpr connected) color
    ((Correspondence.arcs_coloring es color).mpr proper) v z t

end Data

namespace Correspondence

private def AlternatingEdges {X : Type} (mate : X → Option X) (adj : X → X → Prop)
    (path : List X) : Prop :=
  ∀ i (hi : i+1 < path.length), adj path[i] path[i+1] ∧
    (if i % 2 = 0 then mate path[i] ≠ some path[i+1] else mate path[i] = some path[i+1])

private theorem alternating_extend {X : Type} (mate : X → Option X) (adj : X → X → Prop)
    (path : List X) (k : ℕ) (length : path.length = 2*k+2)
    (alternating : AlternatingEdges mate adj path) (y z t : X)
    (last : path.getLast? = some y) (paired : mate y = some z)
    (matchedEdge : adj y z) (finalEdge : adj z t) (unmatched : mate z ≠ some t) :
    AlternatingEdges mate adj (path ++ [z,t]) := by
  intro i hi
  have bound : i+1 < path.length+2 := by simpa using hi
  by_cases old : i+1 < path.length
  · simpa only [List.getElem_append_left (show i < path.length by omega),
      List.getElem_append_left old] using alternating i old
  · by_cases boundary : i+1 = path.length
    · have left : (path ++ [z,t])[i] = y := by
        rw [List.getElem_append_left (by omega)]
        have lastIndex : path.length-1 = i := by omega
        rw [List.getLast?_eq_getElem?, lastIndex, List.getElem?_eq_getElem (by omega)] at last
        exact Option.some.inj last
      have right : (path ++ [z,t])[i+1] = z := by
        rw [List.getElem_append_right (by omega)]
        simp [boundary]
      have odd : i % 2 ≠ 0 := by omega
      simpa only [left,right,odd,ite_false] using And.intro matchedEdge paired
    · have index : i = path.length := by omega
      have even : i % 2 = 0 := by omega
      have left : (path ++ [z,t])[i] = z := by
        rw [List.getElem_append_right (by omega)]
        simp [index]
      have right : (path ++ [z,t])[i+1] = t := by
        rw [List.getElem_append_right (by omega)]
        simp [index]
      simpa only [left,right,even,ite_true] using And.intro finalEdge unmatched

private theorem prefix_head {X : Type} (m : TwoMatching.PartialMatching X) (adj : X → X → Prop)
    {r x : X} (walk : TwoMatching.AlternatingPrefix m adj r x) : walk.vertices.head? = some r := by
  induction walk with
  | start => rfl
  | step previous y z _ _ _ _ ih =>
    simp only [TwoMatching.AlternatingPrefix.vertices, List.head?_append, ih, Option.some_or]

private theorem prefix_finish {X : Type} (m : TwoMatching.PartialMatching X) (adj : X → X → Prop)
    {r x : X} (walk : TwoMatching.AlternatingPrefix m adj r x) (target : X)
    (finalEdge : adj x target) (unmatched : m.mate x ≠ some target) :
    (∃ k, (walk.vertices ++ [target]).length = 2*k+2) ∧
      AlternatingEdges m.mate adj (walk.vertices ++ [target]) := by
  induction walk generalizing target with
  | start =>
    refine ⟨⟨0,rfl⟩,?_⟩
    intro i hi
    have zero : i = 0 := by simpa [TwoMatching.AlternatingPrefix.vertices] using hi
    subst i
    exact ⟨finalEdge,unmatched⟩
  | step previous y z edge unused paired matched ih =>
    obtain ⟨⟨k,hk⟩,alternating⟩ := ih y edge unused
    have same : (previous.vertices ++ [y,z]) ++ [target] =
        (previous.vertices ++ [y]) ++ [z,target] := by simp only [List.append_assoc, List.cons_append, List.nil_append]
    change (∃ k, ((previous.vertices ++ [y,z]) ++ [target]).length = 2*k+2) ∧
      AlternatingEdges m.mate adj ((previous.vertices ++ [y,z]) ++ [target])
    rw [same]
    refine ⟨⟨k+1,by simp only [List.length_append, List.length_cons, List.length_nil] at hk ⊢; omega⟩,?_⟩
    exact alternating_extend m.mate adj _ k hk alternating y z target (by simp)
      paired matched finalEdge unmatched

end Correspondence

namespace Correspondence

theorem augmenting_path {V : Type} {d : ℕ} (es : List (Data.Edge V d))
    (m : TwoMatching.PartialMatching (V × Data.Lattice d)) (root : V × Data.Lattice d)
    (path : TwoMatching.AugmentingPath m
      (PeriodicLatticeGraph.UndirectedAdj (es.map (arc V d))) root) :
    Data.IsAugmentingPath es m.mate root path.vertices := by
  obtain ⟨length,edges⟩ := prefix_finish m _ path.walk path.target path.final_edge path.final_unmatched
  refine ⟨path.simple,?_,path.root_free,?_,length,?_⟩
  · simp only [TwoMatching.AugmentingPath.vertices, List.head?_append, prefix_head, Option.some_or]
  · intro last h
    have same : path.target = last := by
      simpa only [TwoMatching.AugmentingPath.vertices, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Option.some.injEq] using h
    exact same ▸ path.target_free
  · intro i hi
    obtain ⟨edge,alternating⟩ := edges i hi
    exact ⟨(arcs_adj es _ _).mp edge,alternating⟩

end Correspondence

namespace Data

theorem bounded_augmenting_path {V : Type} [DecidableEq V] [Fintype V] {d : ℕ}
    (es : List (Edge V d)) (locality : CoordinateLocal es)
    (perfect : HasPerfectMatching es)
    (mate : V × Lattice d → Option (V × Lattice d))
    (matching : IsPartialMatching es mate) (periodic : IsPeriodOne mate)
    (root : V × Lattice d) (free : mate root = none) :
    ∃ path : List (V × Lattice d), IsAugmentingPath es mate root path ∧
      ∀ x ∈ path, ∀ y ∈ path, ∀ i, (x.2 i-y.2 i).natAbs ≤ 2*d*es.length := by
  let arcs := es.map (Correspondence.arc V d)
  have localArcs : PeriodicLatticeGraph.Local arcs := by
    intro e he i
    obtain ⟨e,mem,rfl⟩ := List.mem_map.mp he
    exact locality e mem i
  obtain ⟨p,involutive,irreflexive,supported⟩ := perfect
  have perfectArcs : PeriodicLatticeGraph.HasPerfectMatching arcs :=
    ⟨⟨p,involutive,irreflexive⟩,fun u => (Correspondence.arcs_adj es _ _).mpr (supported u)⟩
  let m : PeriodicLatticeGraph.PeriodOneMatching arcs :=
    { mate := mate
      symmetric := fun u v h => (matching.1 u v h).1
      irreflexive := matching.2
      supported := fun u v h => (Correspondence.arcs_adj es _ _).mpr (matching.1 u v h).2
      periodic := periodic }
  obtain ⟨path,bound⟩ := PeriodicLatticeGraph.bounded_augmenting_path arcs localArcs perfectArcs m root free
  refine ⟨path.vertices,Correspondence.augmenting_path es m.toPartialMatching root path,?_⟩
  simpa only [PeriodicLatticeGraph.DiameterAtMost,arcs,List.length_map] using bound

end Data

end LeanTrominoes.GraphAbstractBridge
