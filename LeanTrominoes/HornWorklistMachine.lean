/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornWorklistPotential
import LeanTrominoes.HornWorklistIndex

/-! # The indexed Horn worklist machine

Functions denote random-access arrays, not closure-based lookup programs.
Lists denote linked work stacks. The cost model charges indexed reads/writes,
scalar arithmetic, tests, and link allocation/access as unit RAM operations.
-/
namespace LeanTrominoes.Horn.Worklist
/-- An executable dense-index enumeration, separate from unordered finite sets. -/
class Enumeration (R : Type*) where
  values : List R
  nodup : values.Nodup
  complete : ∀ r, r ∈ values

instance (m : Nat) : Enumeration (Fin m) where
  values := List.finRange m
  nodup := List.nodup_finRange m
  complete r := List.mem_finRange r

theorem enumeration_finset {R : Type*} [Fintype R] [DecidableEq R] [Enumeration R] :
    (Enumeration.values : List R).toFinset=Finset.univ := by
  ext r
  simp [Enumeration.complete r]

theorem enumeration_length {R : Type*} [Fintype R] [DecidableEq R] [Enumeration R] :
    (Enumeration.values : List R).length=Fintype.card R := by
  rw [← List.toFinset_card_of_nodup Enumeration.nodup,enumeration_finset,Finset.card_univ]

variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R]

structure State (A R : Type*) where
  seen : A → Bool
  counter : R → Nat
  queue : List A

def initialWithIndex (tables : Index A R) (head : R → A) : State A R :=
  ⟨fun _ => false,tables.counter,
    (Enumeration.values.filter (fun r => decide (tables.counter r=0))).map head⟩

def initial (edges : List (A × R)) (head : R → A) : State A R :=
  initialWithIndex (index edges) head

def advance (buckets : A → List R) (head : R → A) (s : State A R) : State A R :=
  match s.queue with
  | [] => s
  | a::rest =>
    if s.seen a then { s with queue := rest }
    else
      let next := tick s.counter (buckets a)
      ⟨Function.update s.seen a true,next.1,next.2.map head++rest⟩

def potential (s : State A R) : Nat := s.queue.length+(positive s.counter).card

theorem potential_advance (buckets : A → List R) (head : R → A) (s : State A R) (nonempty : s.queue ≠ []) :
    potential (advance buckets head s)+1=potential s := by
  cases queue : s.queue with
  | nil => exact (nonempty queue).elim
  | cons a rest =>
    cases seen : s.seen a with
    | true => simp [advance,queue,seen,potential]; omega
    | false =>
      have balance := tick_balance s.counter (buckets a)
      simp only [advance,queue,seen,Bool.false_eq_true,if_false,potential,List.length_append,List.length_map,List.length_cons]
      omega

def run (buckets : A → List R) (head : R → A) : Nat → State A R → State A R
  | 0,s => s
  | n+1,s => if s.queue=[] then s else run buckets head n (advance buckets head s)

theorem run_empty (buckets : A → List R) (head : R → A) (fuel : Nat) (s : State A R)
    (enough : potential s≤fuel) : (run buckets head fuel s).queue=[] := by
  induction fuel generalizing s with
  | zero =>
    simp only [run]
    have : s.queue.length=0 := by simp only [potential] at enough; omega
    exact List.length_eq_zero_iff.mp this
  | succ n ih =>
    by_cases empty : s.queue=[]
    · simp [run,empty]
    · rw [run,if_neg empty]
      apply ih
      have bound := potential_advance buckets head s empty
      omega

theorem initial_potential (edges : List (A × R)) (head : R → A) :
    potential (initial edges head)=Fintype.card R := by
  have length : (Enumeration.values.filter (fun r : R => decide ((index edges).counter r=0))).length =
      (Finset.univ.filter (fun r : R => (index edges).counter r=0)).card := by
    rw [← List.toFinset_card_of_nodup (Enumeration.nodup.filter _)]
    simp [List.toFinset_filter,enumeration_finset]
  simp only [potential,initial,initialWithIndex,List.length_map,length,positive]
  have split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset R))
    (fun r : R => (index edges).counter r=0)
  simpa only [Nat.pos_iff_ne_zero,Finset.card_univ] using split

def solve (edges : List (A × R)) (head : R → A) : State A R :=
  let tables := index edges
  run tables.bucket head (Fintype.card R) (initialWithIndex tables head)

theorem solve_empty (edges : List (A × R)) (head : R → A) : (solve edges head).queue=[] :=
  run_empty _ _ _ _ (by change potential (initial edges head) ≤ Fintype.card R; rw [initial_potential])

end LeanTrominoes.Horn.Worklist
