/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWorklistSemantics
import LeanTrominoes.SAT.Horn.HornWorklistRAM

/-! # Stack propagation used by the Horn RAM program

The RAM pushes a ready head immediately. Consequently the new heads appear in
reverse occurrence order on its work stack. Queue membership, counters, and
potential agree with the established worklist semantics. This module proves
that correspondence, without asserting an instruction-level time bound.
-/
namespace LeanTrominoes.Horn.Worklist
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R]

def stackTick (head : R → A) (counter : R → ℕ) : List R → List A → (R → ℕ) × List A
  | [],stack => (counter,stack)
  | r::events,stack => stackTick head (Function.update counter r (counter r-1)) events
      (if counter r=1 then head r::stack else stack)

omit [Fintype A] [Fintype R] [DecidableEq A] [Enumeration R] in
theorem stackTick_eq (head : R → A) (counter : R → ℕ) (events : List R) (stack : List A) :
    stackTick head counter events stack=
      ((tick counter events).1,(tick counter events).2.reverse.map head++stack) := by
  induction events generalizing counter stack with
  | nil => simp [stackTick,tick]
  | cons r events ih =>
    simp only [stackTick,tick,ih]
    split <;> simp [List.reverse_cons,List.map_append,List.append_assoc]

def stackAdvance (buckets : A → List R) (head : R → A) (s : State A R) : State A R :=
  match s.queue with
  | [] => s
  | a::rest =>
    if s.seen a then {s with queue := rest}
    else
      let next := stackTick head s.counter (buckets a) rest
      ⟨Function.update s.seen a true,next.1,next.2⟩

omit [Fintype A] [Fintype R] [Enumeration R] in
/-- All observable differences from the established machine are stack order. -/
theorem stackAdvance_agrees (buckets : A → List R) (head : R → A) (s : State A R) :
    (stackAdvance buckets head s).seen=(advance buckets head s).seen ∧
    (stackAdvance buckets head s).counter=(advance buckets head s).counter ∧
    (stackAdvance buckets head s).queue.Perm (advance buckets head s).queue := by
  cases queue : s.queue with
  | nil => simp [stackAdvance,advance,queue]
  | cons a rest =>
    cases seen : s.seen a <;> simp only [stackAdvance,advance,queue,seen,stackTick_eq]
    · simp only [Bool.false_eq_true,ite_false,true_and]
      exact ((List.reverse_perm (tick s.counter (buckets a)).2).map head).append_right rest
    · simp

omit [Fintype A] [Fintype R] [DecidableEq A] [Enumeration R] in
/-- The correctness invariant depends on queue membership, not queue order. -/
theorem invariant_reorder (edges : List (A × R)) (head : R → A) (s t : State A R)
    (seen : t.seen=s.seen) (counter : t.counter=s.counter) (queue : t.queue.Perm s.queue)
    (inv : Invariant edges head s) : Invariant edges head t := by
  have covered (a : A) : Covered t a ↔ Covered s a := by
    simp only [Covered,seen,queue.mem_iff]
  exact ⟨by simpa [counter,seen] using inv.counters,
    fun r zero => (covered _).mpr (inv.ready r (by simpa [counter] using zero)),
    fun model closed a present => inv.sound model closed a ((covered a).mp present)⟩

theorem stackAdvance_invariant (edges : List (A × R)) (head : R → A) (s : State A R)
    (inv : Invariant edges head s) : Invariant edges head (stackAdvance (index edges).bucket head s) := by
  obtain ⟨seen,counter,queue⟩ := stackAdvance_agrees (index edges).bucket head s
  exact invariant_reorder edges head _ _ seen counter queue (advance_invariant edges head s inv)

theorem stackAdvance_potential (buckets : A → List R) (head : R → A) (s : State A R)
    (nonempty : s.queue≠[]) : potential (stackAdvance buckets head s)+1=potential s := by
  obtain ⟨_,counter,queue⟩ := stackAdvance_agrees buckets head s
  have same : potential (stackAdvance buckets head s)=potential (advance buckets head s) := by
    simp only [potential,counter,queue.length_eq]
  rw [same]
  exact potential_advance buckets head s nonempty

def stackRun (buckets : A → List R) (head : R → A) : ℕ → State A R → State A R
  | 0,s => s
  | n+1,s => if s.queue=[] then s else stackRun buckets head n (stackAdvance buckets head s)

theorem stackRun_invariant (edges : List (A × R)) (head : R → A) (fuel : ℕ) (s : State A R)
    (inv : Invariant edges head s) : Invariant edges head (stackRun (index edges).bucket head fuel s) := by
  induction fuel generalizing s with
  | zero => exact inv
  | succ fuel ih =>
    simp only [stackRun]
    split
    · exact inv
    · exact ih _ (stackAdvance_invariant edges head s inv)

theorem stackRun_empty (buckets : A → List R) (head : R → A) (fuel : ℕ) (s : State A R)
    (enough : potential s≤fuel) : (stackRun buckets head fuel s).queue=[] := by
  induction fuel generalizing s with
  | zero =>
    simp only [stackRun]
    have zero : s.queue.length=0 := by simp only [potential] at enough; omega
    exact List.length_eq_zero_iff.mp zero
  | succ fuel ih =>
    simp only [stackRun]
    split
    · assumption
    · apply ih
      have drop := stackAdvance_potential buckets head s (by assumption)
      omega

/-- At termination the marked atoms form the least closed set. This is the
semantic endpoint needed by the machine simulation for negative Horn clauses. -/
theorem stackRun_closed (edges : List (A × R)) (head : R → A) (fuel : ℕ) (s : State A R)
    (inv : Invariant edges head s) (enough : potential s≤fuel) :
    Closed edges head (fun a => (stackRun (index edges).bucket head fuel s).seen a=true) := by
  intro r premises
  have preserved := stackRun_invariant edges head fuel s inv
  have zero := (missing_zero edges _ r).mpr premises
  rw [← preserved.counters] at zero
  have ready := preserved.ready r zero
  simpa only [Covered,stackRun_empty _ _ _ _ enough,List.not_mem_nil,or_false] using ready

/-- Scanning the rules in increasing order and pushing facts produces the
reverse of the original initial queue. -/
def stackInitial (edges : List (A × R)) (head : R → A) : State A R :=
  {initial edges head with queue := (initial edges head).queue.reverse}

theorem stackInitial_invariant (edges : List (A × R)) (head : R → A) :
    Invariant edges head (stackInitial edges head) :=
  invariant_reorder edges head (initial edges head) (stackInitial edges head) rfl rfl
    (List.reverse_perm _) (initial_invariant edges head)

theorem stackInitial_potential (edges : List (A × R)) (head : R → A) :
    potential (stackInitial edges head)=Fintype.card R := by
  simpa only [stackInitial,potential,List.length_reverse] using initial_potential edges head

def stackSolve (edges : List (A × R)) (head : R → A) : State A R :=
  stackRun (index edges).bucket head (Fintype.card R) (stackInitial edges head)

theorem stackSolve_invariant (edges : List (A × R)) (head : R → A) :
    Invariant edges head (stackSolve edges head) :=
  stackRun_invariant edges head _ _ (stackInitial_invariant edges head)

theorem stackSolve_empty (edges : List (A × R)) (head : R → A) : (stackSolve edges head).queue=[] :=
  stackRun_empty _ _ _ _ (by rw [stackInitial_potential])

theorem stackSolve_closed (edges : List (A × R)) (head : R → A) :
    Closed edges head (fun a => (stackSolve edges head).seen a=true) :=
  stackRun_closed edges head _ _ (stackInitial_invariant edges head) (by rw [stackInitial_potential])

theorem stackSolve_least (edges : List (A × R)) (head : R → A)
    (model : A → Prop) (closed : Closed edges head model) (a : A)
    (present : (stackSolve edges head).seen a=true) : model a :=
  (stackSolve_invariant edges head).sound model closed a (Or.inl present)

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R] in
theorem closed_reverse (edges : List (A × R)) (head : R → A) (model : A → Prop) :
    Closed edges.reverse head model ↔ Closed edges head model := by
  simp only [Closed,List.mem_reverse]

end LeanTrominoes.Horn.Worklist
