/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornWorklistMachine

/-! # Soundness and completeness of indexed Horn propagation -/
namespace LeanTrominoes.Horn.Worklist
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R]

def Closed (edges : List (A × R)) (head : R → A) (model : A → Prop) : Prop :=
  ∀ r, (∀ a, (a,r) ∈ edges → model a) → model (head r)

def Covered (s : State A R) (a : A) : Prop := s.seen a=true ∨ a ∈ s.queue

structure Invariant (edges : List (A × R)) (head : R → A) (s : State A R) : Prop where
  counters : ∀ r, s.counter r=missing edges s.seen r
  ready : ∀ r, s.counter r=0 → Covered s (head r)
  sound : ∀ model, Closed edges head model → ∀ a, Covered s a → model a

theorem initial_invariant (edges : List (A × R)) (head : R → A) : Invariant edges head (initial edges head) := by
  constructor
  · exact index_counter edges
  · intro r hr
    right
    apply List.mem_map.mpr
    refine ⟨r,?_,rfl⟩
    exact List.mem_filter.mpr ⟨Enumeration.complete r,by simpa [initial,initialWithIndex] using hr⟩
  · intro model closed a covered
    rcases covered with seen | queued
    · simp [initial,initialWithIndex] at seen
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp queued
      have zero := of_decide_eq_true (List.mem_filter.mp hr).2
      rw [index_counter,missing_zero] at zero
      apply closed r
      intro b member
      have impossible := zero b member
      simp at impossible

theorem mark_seen (seen : A → Bool) (a b : A) :
    Function.update seen a true b=true ↔ b=a ∨ seen b=true := by
  by_cases h : b=a <;> simp [Function.update_apply,h]

theorem advance_invariant (edges : List (A × R)) (head : R → A) (s : State A R)
    (inv : Invariant edges head s) : Invariant edges head (advance (index edges).bucket head s) := by
  cases queue : s.queue with
  | nil => simpa [advance,queue] using inv
  | cons a rest =>
    cases seen : s.seen a with
    | true =>
      simp only [advance,queue,seen,if_true]
      change Invariant edges head { s with queue := rest }
      constructor
      · exact inv.counters
      · intro r zero
        rcases inv.ready r zero with old | queued
        · exact Or.inl old
        · rw [queue,List.mem_cons] at queued
          rcases queued with eq | mem
          · exact Or.inl (by simpa only [eq] using seen)
          · exact Or.inr mem
      · intro model closed b covered
        apply inv.sound model closed b
        rcases covered with old | queued
        · exact Or.inl old
        · exact Or.inr (by rw [queue]; exact List.mem_cons_of_mem a queued)
    | false =>
      simp only [advance,queue,seen,Bool.false_eq_true,if_false]
      let next := tick s.counter ((index edges).bucket a)
      let marked := Function.update s.seen a true
      let after : State A R := ⟨marked,next.1,next.2.map head++rest⟩
      change Invariant edges head after
      have counts (r : R) : next.1 r=missing edges marked r := by
        have removal := missing_mark edges s.seen a seen r
        dsimp only [next]
        rw [tick_counter,index_bucket_count,inv.counters]
        dsimp only [marked]
        omega
      have oldSeen (b : A) (hb : s.seen b=true) : marked b=true := (mark_seen s.seen a b).mpr (Or.inr hb)
      have current (model : A → Prop) (closed : Closed edges head model) : model a :=
        inv.sound model closed a (Or.inr (by rw [queue]; simp))
      have markedSound (model : A → Prop) (closed : Closed edges head model) (b : A) (hb : marked b=true) : model b := by
        rcases (mark_seen s.seen a b).mp hb with eq | old
        · simpa only [eq] using current model closed
        · exact inv.sound model closed b (Or.inl old)
      constructor
      · exact counts
      · intro r zero
        by_cases old : s.counter r=0
        · rcases inv.ready r old with known | queued
          · exact Or.inl (oldSeen _ known)
          · rw [queue,List.mem_cons] at queued
            rcases queued with eq | mem
            · left; exact (mark_seen s.seen a _).mpr (Or.inl eq)
            · right; exact List.mem_append_right _ mem
        · right
          apply List.mem_append_left
          apply List.mem_map.mpr
          exact ⟨r,(tick_ready_mem s.counter ((index edges).bucket a) r).mpr ⟨by omega,zero⟩,rfl⟩
      · intro model closed b covered
        rcases covered with known | queued
        · exact markedSound model closed b known
        · rcases List.mem_append.mp queued with new | old
          · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp new
            have zero := ((tick_ready_mem s.counter ((index edges).bucket a) r).mp hr).2
            rw [counts,missing_zero] at zero
            exact closed r (fun x hx => markedSound model closed x (zero x hx))
          · exact inv.sound model closed b (Or.inr (by rw [queue]; exact List.mem_cons_of_mem a old))

theorem run_invariant (edges : List (A × R)) (head : R → A) (fuel : Nat) (s : State A R)
    (inv : Invariant edges head s) : Invariant edges head (run (index edges).bucket head fuel s) := by
  induction fuel generalizing s with
  | zero => exact inv
  | succ n ih =>
    rw [run]
    split
    · exact inv
    · exact ih _ (advance_invariant edges head s inv)

theorem solve_invariant (edges : List (A × R)) (head : R → A) : Invariant edges head (solve edges head) :=
  run_invariant edges head _ _ (initial_invariant edges head)

theorem solve_closed (edges : List (A × R)) (head : R → A) :
    Closed edges head (fun a => (solve edges head).seen a=true) := by
  intro r premises
  have inv := solve_invariant edges head
  have zero := (missing_zero edges (solve edges head).seen r).mpr premises
  rw [← inv.counters] at zero
  have covered := inv.ready r zero
  simpa only [Covered,solve_empty,List.not_mem_nil,or_false] using covered

theorem solve_least (edges : List (A × R)) (head : R → A) (model : A → Prop)
    (closed : Closed edges head model) (a : A) (known : (solve edges head).seen a=true) : model a :=
  (solve_invariant edges head).sound model closed a (Or.inl known)

end LeanTrominoes.Horn.Worklist
