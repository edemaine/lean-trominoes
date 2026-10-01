/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthWork

/-! # Linear indexed-RAM cost of the breadth-first search -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def Outcome.cost : Outcome L → Nat
  | .layers _ _ c => c
  | .deficient _ _ c => c
  | .exhausted c => c

def Outcome.addCost (c : Nat) : Outcome L → Outcome L
  | .layers d k a => .layers d k (c+a)
  | .deficient d k a => .deficient d k (c+a)
  | .exhausted a => .exhausted (c+a)

theorem Outcome.cost_addCost (c : Nat) (o : Outcome L) : (o.addCost c).cost=c+o.cost := by
  cases o <;> rfl

theorem wave_budget (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (positive : 0 < freeCount) (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    (wave buckets matching depth frontier distance).cost+
      (wave buckets matching depth frontier distance).next.length+5+
      20*work buckets (wave buckets matching depth frontier distance).distance (depth+1) ≤
      20*work buckets distance depth := by
  have cost := expand_cost buckets matching depth frontier (⟨distance,[],false,0⟩ : Wave L)
  have next := expand_next_length buckets matching depth frontier (⟨distance,[],false,0⟩ : Wave L)
  have balance := work_balance buckets matching freeCount depth frontier distance inv
  have front := frontier_length buckets matching freeCount depth frontier distance inv
  change (wave buckets matching depth frontier distance).cost ≤
    0+4*frontier.length+10*(frontier.map (fun l => (buckets l).length)).sum+1 at cost
  change (wave buckets matching depth frontier distance).next.length ≤
    0+(frontier.map (fun l => (buckets l).length)).sum at next
  omega

theorem run_succ (buckets : L → List R) (matching : State L R) (freeCount fuel depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    run buckets matching freeCount (fuel+1) depth frontier distance=
      if (wave buckets matching depth frontier distance).terminal then
        .layers (wave buckets matching depth frontier distance).distance (depth+1)
          ((wave buckets matching depth frontier distance).cost+3)
      else if (wave buckets matching depth frontier distance).next.length < freeCount then
        .deficient (wave buckets matching depth frontier distance).distance depth
          ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+4)
      else (run buckets matching freeCount fuel (depth+1)
        (wave buckets matching depth frontier distance).next
        (wave buckets matching depth frontier distance).distance).addCost
        ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+5) := by
  simp only [run,wave]
  split
  · rfl
  · split
    · rfl
    · cases run buckets matching freeCount fuel (depth+1)
        (expand buckets matching depth frontier ⟨distance,[],false,0⟩).next
        (expand buckets matching depth frontier ⟨distance,[],false,0⟩).distance <;> rfl

theorem run_cost_bound (buckets : L → List R) (matching : State L R) (freeCount : Nat)
    (positive : 0 < freeCount) (fuel depth : Nat) (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    (run buckets matching freeCount fuel depth frontier distance).cost ≤ 20*work buckets distance depth+1 := by
  induction fuel generalizing depth frontier distance with
  | zero => simp [run,Outcome.cost]
  | succ fuel ih =>
    have budget := wave_budget buckets matching freeCount depth positive frontier distance inv
    rw [run_succ]
    cases terminal : (wave buckets matching depth frontier distance).terminal with
    | true => simp only [if_true,Outcome.cost]; omega
    | false =>
      simp only [Bool.false_eq_true,if_false]
      by_cases deficient : (wave buckets matching depth frontier distance).next.length < freeCount
      · simp only [deficient,if_true,Outcome.cost]; omega
      · simp only [deficient,if_false,Outcome.cost_addCost]
        have nextInv := wave_invariant buckets matching freeCount depth frontier distance inv terminal (by omega)
        have later := ih (depth+1) (wave buckets matching depth frontier distance).next
          (wave buckets matching depth frontier distance).distance nextInv
        omega

theorem initial_work (buckets : L → List R) (matching : State L R) :
    work buckets (initialDistance matching) 0=(∑ l, (buckets l).length)+Fintype.card L := by
  simp [work,past,Finset.sum_add_distrib]

theorem search_cost_bound (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R)
    (positive : 0 < (freeVertices vertices matching).length) :
    (search vertices buckets matching).cost ≤ 20*((∑ l, (buckets l).length)+Fintype.card L)+1 := by
  have bound := run_cost_bound buckets matching _ positive vertices.length 0
    (freeVertices vertices matching) (initialDistance matching)
    (initial_invariant vertices nodup complete buckets matching)
  simpa [search,initial_work] using bound

end LeanTrominoes.BipartiteMatching.BreadthSearch
