/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingSolverCorrect
import LeanTrominoes.PeriodicMatchingSelection

/-! # Theorem 4.7: indexed periodic perfect matching

Inputs use dense left/right indices and a list of protoedge records; the
lattice dimension and offsets are arbitrary. The RAM has constant-time typed
indices, array reads/writes, scalars, and linked-list cells. Edge vectors stay
in the input store and the answer stores references. Charges and phase traces
are ghost instrumentation. This is not a bit-cost or Lean VM runtime claim.
-/
namespace LeanTrominoes.PeriodicBipartite

structure MatchingResult (L R : Type*) (d : Nat) where
  table : Option (L → Option (Edge L R d))
  cost : Nat

/-- The size check precedes all vertex-array allocation. -/
def matchingSolver {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) : MatchingResult (Fin n) (Fin m) d :=
  let inputScan := 2*edges.length+5
  if n ≠ m then ⟨none,inputScan⟩ else if edges.length < n then ⟨none,inputScan⟩ else
    let result := BipartiteMatching.compute (List.finRange n) (buckets edges)
    let setup := inputScan+24*edges.length+10*n+6*m+5
    match result.matching with
    | none => ⟨none,setup+result.cost+2⟩
    | some state =>
      let selected := executeSelect state edges
      ⟨some selected.1,setup+result.cost+selected.2+4*n+3⟩

def MatchingResultSpec {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) :
    Option (Fin n → Option (Edge (Fin n) (Fin m) d)) → Prop
  | none => ¬ HasPerfectMatching edges
  | some table => TableSpec edges table

theorem matchingSolver_spec {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) :
    MatchingResultSpec edges (matchingSolver edges).table := by
  unfold matchingSolver
  dsimp only
  by_cases unequal : n ≠ m
  · rw [if_pos unequal]
    simp only [MatchingResultSpec]
    change ¬ HasPerfectMatching edges
    intro perfect
    have equal := quotient_card edges ((perfect_iff_quotient edges).mp perfect)
    simp only [Fintype.card_fin] at equal
    exact unequal equal
  · simp only [unequal,if_false]
    by_cases sparse : edges.length < n
    · simp only [sparse,if_true,MatchingResultSpec]
      intro perfect
      have bound := quotient_edges edges ((perfect_iff_quotient edges).mp perfect)
      simp only [Fintype.card_fin] at bound
      omega
    · simp only [sparse,if_false]
      have spec := BipartiteMatching.compute_spec (List.finRange n) (List.nodup_finRange n)
        (fun l => List.mem_finRange l) (buckets edges)
      cases found : (BipartiteMatching.compute (List.finRange n) (buckets edges)).matching with
      | none =>
        simp only [found,BipartiteMatching.OutputSpec] at spec
        intro perfect
        exact spec ((finite_iff_quotient edges).mpr ((perfect_iff_quotient edges).mp perfect))
      | some state =>
        simp only [found,BipartiteMatching.OutputSpec] at spec
        change TableSpec edges (executeSelect state edges).1
        rw [executeSelect_table]
        exact select_period_one state edges spec.1 spec.2.1 spec.2.2 (by simp only [Fintype.card_fin]; omega)

theorem matchingSolver_iff {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) :
    (matchingSolver edges).table.isSome=true ↔ HasPerfectMatching edges := by
  have spec := matchingSolver_spec edges
  cases found : (matchingSolver edges).table with
  | none => simp only [found,MatchingResultSpec] at spec; simp [spec]
  | some table =>
    simp only [found,MatchingResultSpec] at spec
    have yes := period_one_to_perfect edges (spec.period_one edges table)
    simp [yes]

/-- Explicit uniform bound, including indexing, initialization, and edge selection. -/
theorem matchingSolver_cost {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) :
    (matchingSolver edges).cost ≤ 1000*(edges.length+1)*(Nat.sqrt (n+m)+1) := by
  unfold matchingSolver
  dsimp only
  by_cases unequal : n ≠ m
  · rw [if_pos unequal]
    nlinarith [show 1 ≤ Nat.sqrt (n+m)+1 by omega]
  · simp only [unequal,if_false]
    by_cases sparse : edges.length < n
    · simp only [sparse,if_true]
      nlinarith [show 1 ≤ Nat.sqrt (n+m)+1 by omega]
    · simp only [sparse,if_false]
      have balanced : n=m := by omega
      have leftBound : n ≤ edges.length := by omega
      have rightBound : m ≤ edges.length := by omega
      have room : 100*(edges.length+1) ≤ 100*(edges.length+1)*(Nat.sqrt (n+m)+1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (100*(edges.length+1)) (show 1 ≤ Nat.sqrt (n+m)+1 by omega)
      have bound := BipartiteMatching.compute_cost (List.finRange n) (List.nodup_finRange n)
        (fun l => List.mem_finRange l) (buckets edges)
      rw [buckets_volume] at bound
      simp only [Fintype.card_fin] at bound
      have root : Nat.sqrt n+1 ≤ Nat.sqrt (n+m)+1 := by
        have := Nat.sqrt_le_sqrt (show n ≤ n+m by omega)
        omega
      have budget : (BipartiteMatching.compute (List.finRange n) (buckets edges)).cost ≤
          900*(edges.length+1)*(Nat.sqrt (n+m)+1) := by
        have slots : edges.length+n+m+1 ≤ 3*(edges.length+1) := by omega
        have bound' := bound.trans (Nat.mul_le_mul
          (Nat.mul_le_mul_left 300 slots) root)
        nlinarith
      cases found : (BipartiteMatching.compute (List.finRange n) (buckets edges)).matching with
      | none =>
        change 2*edges.length+5+24*edges.length+10*n+6*m+5+
          (BipartiteMatching.compute (List.finRange n) (buckets edges)).cost+2
          ≤ 1000*(edges.length+1)*(Nat.sqrt (n+m)+1)
        nlinarith [show 1 ≤ Nat.sqrt (n+m)+1 by omega]
      | some state =>
        simp only [executeSelect_cost]
        change 2*edges.length+5+24*edges.length+10*n+6*m+5+
          (BipartiteMatching.compute (List.finRange n) (buckets edges)).cost+(12*edges.length+1)+4*n+3
          ≤ 1000*(edges.length+1)*(Nat.sqrt (n+m)+1)
        nlinarith [show 1 ≤ Nat.sqrt (n+m)+1 by omega]

/-- The paper's `O(E*sqrt(V))` form for nonempty edge tables; empty inputs take constant time. -/
theorem matchingSolver_edge_sqrt_bound {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d))
    (nonempty : 0 < edges.length) :
    (matchingSolver edges).cost ≤ 4000*edges.length*Nat.sqrt (n+m) := by
  have vertices : 0 < n+m := by
    cases edges with
    | nil => simp at nonempty
    | cons e es => have bound := e.left.isLt; omega
  have root := Nat.sqrt_pos.mpr vertices
  have edgeFactor : edges.length+1 ≤ 2*edges.length := by omega
  have rootFactor : Nat.sqrt (n+m)+1 ≤ 2*Nat.sqrt (n+m) := by omega
  have bound := (matchingSolver_cost edges).trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 1000 edgeFactor) rootFactor)
  nlinarith

/-- Decision, finite-table construction, and the complete indexed-RAM bound together. -/
theorem matchingSolver_certified {n m d : Nat} (edges : List (Edge (Fin n) (Fin m) d)) :
    ((matchingSolver edges).table.isSome=true ↔ HasPerfectMatching edges) ∧
    MatchingResultSpec edges (matchingSolver edges).table ∧
    (matchingSolver edges).cost ≤ 1000*(edges.length+1)*(Nat.sqrt (n+m)+1) :=
  ⟨matchingSolver_iff edges,matchingSolver_spec edges,matchingSolver_cost edges⟩

end LeanTrominoes.PeriodicBipartite
