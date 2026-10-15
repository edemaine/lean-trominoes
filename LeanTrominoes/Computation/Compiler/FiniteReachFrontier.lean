/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! # Finite directed reachability needs at most |V| frontier expansions -/
namespace LeanTrominoes.ImplicationGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj] (root : V)

def frontier : Nat → Finset V
  | 0 => {root}
  | k+1 => frontier k ∪ Finset.univ.filter (fun v => ∃ u ∈ frontier k, adj u v)

theorem frontier_subset (k : Nat) : frontier adj root k ⊆ frontier adj root (k+1) :=
  Finset.subset_union_left

theorem frontier_mono : Monotone (frontier adj root) :=
  monotone_nat_of_le_succ (frontier_subset adj root)

theorem root_mem_frontier (k : Nat) : root ∈ frontier adj root k :=
  frontier_mono adj root (Nat.zero_le k) (by simp [frontier])

theorem frontier_stabilizes : ∃ k < Fintype.card V, frontier adj root k=frontier adj root (k+1) := by
  by_contra none
  have different (k : Nat) (hk : k < Fintype.card V) : frontier adj root k ≠ frontier adj root (k+1) := by
    intro same
    exact none ⟨k,hk,same⟩
  have growth (k : Nat) (hk : k < Fintype.card V) :
      (frontier adj root k).card < (frontier adj root (k+1)).card := by
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨frontier_subset adj root k,different k hk⟩)
  have size (k : Nat) (hk : k ≤ Fintype.card V) : k+1 ≤ (frontier adj root k).card := by
    induction k with
    | zero => simp [frontier]
    | succ k ih =>
      have before := ih (by omega)
      have after := growth k (by omega)
      omega
  have impossible := size (Fintype.card V) le_rfl
  have bounded := Finset.card_le_univ (frontier adj root (Fintype.card V))
  omega

/-- A fixed frontier contains every vertex reachable from the root. -/
theorem reachable_mem_frontier (v : V) (reachable : Relation.ReflTransGen adj root v) :
    v ∈ frontier adj root (Fintype.card V) := by
  obtain ⟨k,hk,fixed⟩ := frontier_stabilizes adj root
  have member : v ∈ frontier adj root k := by
    induction reachable with
    | refl => exact root_mem_frontier adj root k
    | @tail w v path edge ih =>
      rw [fixed]
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,ih,edge⟩)
  exact frontier_mono adj root hk.le member

/-- Any invariant maintained by one frontier expansion holds at all bounded reachable vertices. -/
theorem frontier_induction (P : Nat → V → Prop) (base : P 0 root)
    (keep : ∀ k v, P k v → P (k+1) v)
    (step : ∀ k u v, P k u → adj u v → P (k+1) v)
    (k : Nat) (v : V) (member : v ∈ frontier adj root k) : P k v := by
  induction k generalizing v with
  | zero =>
    have equal : v=root := by simpa [frontier] using member
    simpa [equal] using base
  | succ k ih =>
    rcases Finset.mem_union.mp member with old | fresh
    · exact keep k v (ih v old)
    · obtain ⟨_,u,hu,edge⟩ := Finset.mem_filter.mp fresh
      exact step k u v (ih u hu) edge

end LeanTrominoes.ImplicationGraph
