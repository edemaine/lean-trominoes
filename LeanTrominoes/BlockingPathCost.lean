/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathSearch

/-! # Linear indexed-RAM charge for a blocking-path search

A vertex's entire adjacency budget is removed on its first entry. Recursive
calls therefore charge disjoint adjacency lists, including failed branches.
No search or equality on symbolic vertex names is assumed to be constant:
the eventual solver uses explicit finite array indices.
-/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype V]

def work (buckets : Buckets V T) (s : State V T) : Nat :=
  ∑ v, if s.blocked v then 0 else (buckets v).length+1

theorem work_enter (buckets : Buckets V T) (s : State V T) (v : V) (fresh : s.blocked v=false) :
    work buckets (enter s v)+(buckets v).length+1=work buckets s := by
  have point (w : V) : (if s.blocked w then 0 else (buckets w).length+1)=
      (if (enter s v).blocked w then 0 else (buckets w).length+1)+
      (if w=v then (buckets v).length+1 else 0) := by
    by_cases eq : w=v <;> simp [enter,eq,fresh]
  unfold work
  simp_rw [point]
  rw [Finset.sum_add_distrib]
  simp [Nat.add_assoc]

theorem scan_cost_bound (buckets : Buckets V T) (descend : V → State V T → Result V T)
    (bound : ∀ v s, (descend v s).cost+20*work buckets (descend v s).state ≤ 20*work buckets s+2)
    (v : V) (arcs : List (T × Option V)) (s : State V T) :
    (scan descend v arcs s).cost+20*work buckets (scan descend v arcs s).state ≤
      20*work buckets s+12*arcs.length+1 := by
  induction arcs generalizing s with
  | nil => simp [scan] <;> omega
  | cons arc arcs ih =>
    obtain ⟨t,next⟩ := arc
    cases next with
    | none =>
      cases reserved : s.reserved t with
      | true =>
        have later := ih s
        simp only [scan,reserved,if_true,List.length_cons]
        omega
      | false =>
        have equal : work buckets (reserve s t)=work buckets s := rfl
        simp only [scan,reserved,Bool.false_eq_true,if_false,List.length_cons,equal]
        omega
    | some w =>
      have child := bound w s
      cases found : (descend w s).route with
      | none =>
        have later := ih (descend w s).state
        simp only [scan,found,List.length_cons]
        omega
      | some p =>
        simp only [scan,found,List.length_cons]
        omega

theorem search_cost_bound (buckets : Buckets V T) (fuel : Nat) (v : V) (s : State V T) :
    (search buckets fuel v s).cost+20*work buckets (search buckets fuel v s).state ≤
      20*work buckets s+2 := by
  induction fuel generalizing v s with
  | zero => simp [search] <;> omega
  | succ fuel ih =>
    cases blocked : s.blocked v with
    | true => simp [search,blocked] <;> omega
    | false =>
      have budget := scan_cost_bound buckets (search buckets fuel) ih v (buckets v) (enter s v)
      have drop := work_enter buckets s v blocked
      cases found : (scan (search buckets fuel) v (buckets v) (enter s v)).route with
      | none =>
        have same : work buckets (retire (scan (search buckets fuel) v (buckets v) (enter s v)).state v)=
            work buckets (scan (search buckets fuel) v (buckets v) (enter s v)).state := rfl
        simp only [search,blocked,Bool.false_eq_true,if_false,found,same]
        omega
      | some p =>
        simp only [search,blocked,Bool.false_eq_true,if_false,found]
        omega

end LeanTrominoes.BlockingPath
