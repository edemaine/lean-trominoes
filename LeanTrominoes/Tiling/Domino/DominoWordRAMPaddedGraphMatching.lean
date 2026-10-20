/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMPaddedGraph

/-! # Correctness of the fixed-size domino candidate edge table -/
namespace LeanTrominoes.Domino.WordRAM.PaddedGraph
open PeriodicLatticeGraph
variable {n d : ℕ}

abbrev dummy (n d : ℕ) : Fin (n*2^d+1) × Fin (n*2^d+1) := (Fin.last _,Fin.last _)

def liftPair {N : ℕ} (pair : Fin N × Fin N) : Fin (N+1) × Fin (N+1) :=
  (pair.1.castSucc,pair.2.castSucc)

noncomputable def candidateEdges (B : BasisData n d) (c : Candidate n d) :
    List (Fin (n*2^d+1) × Fin (n*2^d+1)) := by
  classical
  exact if Active B c.1 c.2.1 c.2.2.1 then
    [liftPair (coverPair (arc B c.1 c.2.1 c.2.2.1) c.2.2.2),
      liftPair (coverPair (arc B c.1 c.2.1 c.2.2.1) c.2.2.2).swap]
  else [dummy n d,dummy n d]

noncomputable def edges (B : BasisData n d) : List (Fin (n*2^d+1) × Fin (n*2^d+1)) :=
  dummy n d::(candidates n d).flatMap (candidateEdges B)

theorem candidateEdges_length (B : BasisData n d) (c : Candidate n d) : (candidateEdges B c).length=2 := by
  classical
  unfold candidateEdges
  split_ifs <;> rfl

theorem edges_length (B : BasisData n d) : (edges B).length=2*n*n*d*2^d+1 := by
  simp [edges,List.length_flatMap,candidateEdges_length,candidates_length]
  ring

private theorem lift_member (old : List (Fin (n*2^d) × Fin (n*2^d))) (pair : Fin (n*2^d) × Fin (n*2^d))
    (member : pair∈old) : liftPair pair∈BipartiteMatching.DummyVertex.addDummy old := by
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨pair,member,rfl⟩

/-- Padding and duplicate dummy edges preserve exactly the old supported pairs. -/
theorem edges_mem (B : BasisData n d) (valid : B.Valid) (pair : Fin (n*2^d+1) × Fin (n*2^d+1)) :
    pair∈edges B ↔ pair∈BipartiteMatching.DummyVertex.addDummy (PeriodicBipartite.edgePairs (solverEdges B.cellArcs)) := by
  classical
  constructor
  · intro member
    rcases List.mem_cons.mp member with equal | member
    · rw [equal]
      exact List.mem_cons_self
    · obtain ⟨c,_,member⟩ := List.mem_flatMap.mp member
      unfold candidateEdges at member
      split_ifs at member with active
      · have arcMem := active_arc_mem B valid c.1 c.2.1 c.2.2.1 active
        have forward := (solver_pairs_mem B.cellArcs _).mpr ⟨_,arcMem,c.2.2.2,Or.inl rfl⟩
        have backward := (solver_pairs_mem B.cellArcs _).mpr ⟨_,arcMem,c.2.2.2,Or.inr rfl⟩
        rcases (by simpa using member : pair=liftPair (coverPair (arc B c.1 c.2.1 c.2.2.1) c.2.2.2) ∨
          pair=liftPair (coverPair (arc B c.1 c.2.1 c.2.2.1) c.2.2.2).swap) with equal | equal
        · rw [equal]
          exact lift_member _ _ forward
        · rw [equal]
          exact lift_member _ _ backward
      · have equal : pair=dummy n d := by simpa using member
        rw [equal]
        exact List.mem_cons_self
  · intro member
    rcases List.mem_cons.mp member with equal | member
    · exact List.mem_cons.mpr (Or.inl equal)
    · obtain ⟨old,oldMem,equal⟩ := List.mem_map.mp member
      obtain ⟨e,he,phase,orientation⟩ := (solver_pairs_mem B.cellArcs old).mp oldMem
      obtain ⟨direction,active,arcEq⟩ := every_arc_candidate B valid e he
      let c : Candidate n d := (e.source,direction,e.target,phase)
      apply List.mem_cons.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨c,mem_candidates c,?_⟩
      rw [←equal]
      change liftPair old∈if Active B e.source direction e.target then
        [liftPair (coverPair (arc B e.source direction e.target) phase),
          liftPair (coverPair (arc B e.source direction e.target) phase).swap] else [dummy n d,dummy n d]
      rw [if_pos active,arcEq]
      rcases orientation with forward | backward
      · simp [forward]
      · simp [backward]

theorem finite_pairs_iff (old : List (PeriodicBipartite.Edge (Fin n) (Fin n) d)) :
    BipartiteMatching.HasFiniteMatching (BipartiteMatching.DenseSearch.edgeBuckets (PeriodicBipartite.edgePairs old)) ↔
      PeriodicBipartite.HasQuotientMatching old := by
  simp only [BipartiteMatching.HasFiniteMatching,PeriodicBipartite.HasQuotientMatching]
  apply exists_congr
  intro f
  apply forall_congr'
  intro i
  simp [BipartiteMatching.DenseSearch.mem_edgeBuckets,PeriodicBipartite.edgePairs,
    PeriodicBipartite.QuotientAdj,Prod.mk.injEq]

/-- The fixed-length endpoint table decides the original domino tilability
criterion, including holes, repeated candidate records, and empty regions. -/
theorem matching_iff_tileable (B : BasisData n d) (valid : B.Valid) :
    BipartiteMatching.HasFiniteMatching (BipartiteMatching.DenseSearch.edgeBuckets (edges B)) ↔
      Tileable (B.chart valid).region := by
  rw [BipartiteMatching.DummyVertex.matching_congr (edges B) _ (fun l r => edges_mem B valid (l,r)),
    BipartiteMatching.DummyVertex.matching_addDummy,finite_pairs_iff,
    ←PeriodicBipartite.perfect_iff_quotient]
  exact solverEdges_perfect_iff (B.graph valid)

end LeanTrominoes.Domino.WordRAM.PaddedGraph
