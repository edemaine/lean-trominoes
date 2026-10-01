/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingSolverSemantics

/-! # Complete finite matching decision and square-root RAM bound -/
namespace LeanTrominoes.BipartiteMatching
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def compute (vertices : List L) (buckets : L → List R) : SolverResult L R :=
  solve vertices buckets vertices.length empty

theorem compute_spec (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) : OutputSpec buckets (compute vertices buckets).matching := by
  have spec := solve_spec vertices nodup complete buckets vertices.length empty empty_consistent
    (empty_supported (fun l r => r ∈ buckets l)) 0 (noShort_zero buckets empty) (List.length_filter_le _ _)
  exact spec.1

theorem compute_iff (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (balanced : Fintype.card L=Fintype.card R) :
    (compute vertices buckets).matching.isSome=true ↔ HasFiniteMatching buckets := by
  have spec := compute_spec vertices nodup complete buckets
  cases found : (compute vertices buckets).matching with
  | none => simp only [found,OutputSpec] at spec; simp [spec]
  | some s =>
    simp only [found,OutputSpec] at spec
    have yes := full_equiv buckets s spec.1 spec.2.1 balanced spec.2.2
    simp [yes]

theorem compute_cost (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) :
    (compute vertices buckets).cost ≤
      300*((∑ l, (buckets l).length)+Fintype.card L+Fintype.card R+1)*(Nat.sqrt (Fintype.card L)+1) := by
  have spec := solve_spec vertices nodup complete buckets vertices.length empty empty_consistent
    (empty_supported (fun l r => r ∈ buckets l)) 0 (noShort_zero buckets empty) (List.length_filter_le _ _)
  have phases := spec.2.1.length_bound
  have rounds : (solve vertices buckets vertices.length empty).trace.length+1 ≤ 3*(Nat.sqrt (Fintype.card L)+1) := by omega
  have bound := spec.2.2.trans (Nat.mul_le_mul_left (roundBudget buckets) rounds)
  dsimp only [roundBudget] at bound
  change (compute vertices buckets).cost ≤ _ at bound
  convert bound using 1 <;> ring

end LeanTrominoes.BipartiteMatching
