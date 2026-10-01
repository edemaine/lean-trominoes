/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathSemantics
import LeanTrominoes.BlockingPathCost

/-! # A complete disjoint-path blocking phase -/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype V]

structure BatchResult (V T : Type*) where
  state : State V T
  paths : List (Route V T)
  cost : Nat

def batch (buckets : Buckets V T) (fuel : Nat) : List V → State V T → BatchResult V T
  | [],s => ⟨s,[],1⟩
  | v::vs,s =>
    let first := search buckets fuel v s
    let later := batch buckets fuel vs first.state
    ⟨later.state,match first.route with
      | none => later.paths
      | some p => p::later.paths,
     4+first.cost+later.cost⟩

def initial : State V T := ⟨fun _ => false,fun _ => false,fun _ => false⟩

theorem batch_cost_bound (buckets : Buckets V T) (fuel : Nat) (roots : List V) (s : State V T) :
    (batch buckets fuel roots s).cost+20*work buckets (batch buckets fuel roots s).state ≤
      20*work buckets s+6*roots.length+1 := by
  induction roots generalizing s with
  | nil => simp [batch] <;> omega
  | cons v vs ih =>
    have first := search_cost_bound buckets fuel v s
    have later := ih (search buckets fuel v s).state
    simp only [batch,List.length_cons]
    omega

theorem initial_work (buckets : Buckets V T) : work buckets (initial : State V T)=
    (∑ v, (buckets v).length)+Fintype.card V := by
  simp [work,initial,Finset.sum_add_distrib]

/-- Initializing the three arrays is separately charged by the caller. -/
theorem batch_linear (buckets : Buckets V T) (roots : List V) :
    (batch buckets (Fintype.card V) roots initial).cost ≤
      20*((∑ v, (buckets v).length)+Fintype.card V)+6*roots.length+1 := by
  have bound := batch_cost_bound buckets (Fintype.card V) roots initial
  rw [initial_work] at bound
  omega

end LeanTrominoes.BlockingPath
