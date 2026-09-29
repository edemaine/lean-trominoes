/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornWorklistCounters

/-! # One-pass occurrence indexing, retaining duplicate premises -/
namespace LeanTrominoes.Horn.Worklist
variable {A R : Type*} [DecidableEq A] [DecidableEq R]

structure Index (A R : Type*) where
  bucket : A → List R
  counter : R → Nat

def index : List (A × R) → Index A R
  | [] => ⟨fun _ => [],fun _ => 0⟩
  | (a,r)::edges =>
    let old := index edges
    ⟨Function.update old.bucket a (r::old.bucket a),Function.update old.counter r (old.counter r+1)⟩

def missing (edges : List (A × R)) (seen : A → Bool) (r : R) : Nat :=
  edges.countP (fun ar => decide (ar.2=r) && !seen ar.1)

theorem index_counter (edges : List (A × R)) (r : R) :
    (index edges).counter r=missing edges (fun _ => false) r := by
  induction edges with
  | nil => simp [index,missing]
  | cons ar edges ih =>
    rcases ar with ⟨a,s⟩
    by_cases h : r=s
    · subst s; simp [index,missing,List.countP_cons,ih,missing]
    · simpa [index,missing,h,Ne.symm h] using ih

theorem index_bucket_count (edges : List (A × R)) (a : A) (r : R) :
    ((index edges).bucket a).count r=edges.count (a,r) := by
  induction edges with
  | nil => simp [index]
  | cons ar edges ih =>
    rcases ar with ⟨b,s⟩
    by_cases ha : a=b
    · subst b
      by_cases hr : r=s
      · subst s; simp [index,ih]
      · simp [index,List.count_cons,hr,Ne.symm hr,ih]
    · simp [index,Function.update_of_ne ha,List.count_cons,ha,Ne.symm ha,ih]

theorem missing_mark (edges : List (A × R)) (seen : A → Bool) (a : A) (fresh : seen a=false) (r : R) :
    missing edges (Function.update seen a true) r+edges.count (a,r)=missing edges seen r := by
  induction edges with
  | nil => simp [missing]
  | cons ar edges ih =>
    rcases ar with ⟨b,s⟩
    by_cases ha : b=a
    · subst b
      by_cases hr : s=r
      · subst s; simp [missing,List.countP_cons,List.count_cons,fresh] at *; omega
      · simp [missing,List.countP_cons,List.count_cons,fresh,hr,Ne.symm hr] at *; exact ih
    · simp [missing,List.countP_cons,List.count_cons,Function.update_of_ne ha,ha,Ne.symm ha] at *
      omega

theorem missing_zero (edges : List (A × R)) (seen : A → Bool) (r : R) :
    missing edges seen r=0 ↔ ∀ a, (a,r) ∈ edges → seen a=true := by
  simp only [missing,List.countP_eq_zero,Bool.not_eq_true',Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h a ha
    have no := h (a,r) ha
    cases hs : seen a <;> simp_all
  · intro h ar har
    rcases ar with ⟨a,s⟩
    rintro ⟨eq,no⟩
    change s=r at eq
    subst s
    have yes := h a har
    simp_all

theorem index_volume [Fintype A] (edges : List (A × R)) :
    (∑ a, ((index edges).bucket a).length)=edges.length := by
  induction edges with
  | nil => simp [index]
  | cons ar edges ih =>
    rcases ar with ⟨a,r⟩
    have eq (b : A) : ((index ((a,r)::edges)).bucket b).length =
        ((index edges).bucket b).length + if b=a then 1 else 0 := by
      by_cases h : b=a
      · subst b; simp [index]
      · simp [index,Function.update_of_ne h,h]
    simp only [eq,Finset.sum_add_distrib,ih,List.length_cons]
    simp

end LeanTrominoes.Horn.Worklist
