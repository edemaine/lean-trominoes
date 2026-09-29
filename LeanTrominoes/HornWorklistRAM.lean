/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornWorklistMachine

/-! # Linear operation bound in an indexed unit-cost RAM model

Array lookup/update, scalar arithmetic/comparison, and linked-cell operations
cost one unit. `tickCost` charges each counter read/write and conditional ready
push; `queueCost` charges the complete rule-table scan. `totalCost` additionally
charges zeroing both atom arrays and the counter array, building the occurrence
index, running the worklist, and reading the answer. These are RAM costs, not
costs of evaluating the extensional function representation in Lean's VM.
-/
namespace LeanTrominoes.Horn.Worklist.RAM
open Worklist
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R]

-- Eight operations cover event-cell access, counter reads, decrement, write,
-- comparison, and control. A ready-rule cell adds two operations.
def tickCost (c : R → Nat) : List R → Nat
  | [] => 1
  | r::rs => 8+(if c r=1 then 2 else 0)+tickCost (Function.update c r (c r-1)) rs

theorem tickCost_bound (c : R → Nat) (events : List R) : tickCost c events ≤ 10*events.length+1 := by
  induction events generalizing c with
  | nil => simp [tickCost]
  | cons r rs ih =>
    have h := ih (Function.update c r (c r-1))
    simp only [tickCost,List.length_cons]
    split <;> omega

-- Read/test/control per rule; six more operations cover the fact-list cell,
-- its later traversal, head lookup, and final queue-cell allocation.
def queueCost (c : R → Nat) : List R → Nat
  | [] => 1
  | r::rs => 3+(if c r=0 then 6 else 0)+queueCost c rs

theorem queueCost_bound (c : R → Nat) (ids : List R) : queueCost c ids ≤ 9*ids.length+1 := by
  induction ids with
  | nil => simp [queueCost]
  | cons r rs ih => simp only [queueCost,List.length_cons]; split <;> omega

-- Two table reads, two writes, increment, link allocation/access, input
-- access, and loop control per premise occurrence; no search for an index.
def indexCost (edges : List (A × R)) : Nat := 12*edges.length+1

def stepCost (buckets : A → List R) (s : State A R) : Nat :=
  match s.queue with
  | [] => 1
  | a::_ => if s.seen a then 5 else
      10+tickCost s.counter (buckets a)+6*(tick s.counter (buckets a)).2.length

def cost (buckets : A → List R) (head : R → A) : Nat → State A R → Nat
  | 0,_ => 1
  | fuel+1,s => if s.queue=[] then 1 else
      stepCost buckets s+cost buckets head fuel (advance buckets head s)

def unread (buckets : A → List R) (seen : A → Bool) : Nat :=
  ∑ a, if seen a then 0 else (buckets a).length

def work (buckets : A → List R) (s : State A R) : Nat := potential s+unread buckets s.seen

theorem unread_mark (buckets : A → List R) (seen : A → Bool) (a : A) (fresh : seen a=false) :
    unread buckets (Function.update seen a true)+(buckets a).length=unread buckets seen := by
  have point (b : A) : (if seen b then 0 else (buckets b).length)=
      (if Function.update seen a true b then 0 else (buckets b).length)+(if b=a then (buckets a).length else 0) := by
    by_cases eq : b=a <;> simp [Function.update_apply,eq,fresh]
  unfold unread
  simp_rw [point]
  rw [Finset.sum_add_distrib]
  simp

theorem step_budget (buckets : A → List R) (head : R → A) (s : State A R) (nonempty : s.queue ≠ []) :
    stepCost buckets s+20*work buckets (advance buckets head s) ≤ 20*work buckets s := by
  have drop := potential_advance buckets head s nonempty
  cases queue : s.queue with
  | nil => exact (nonempty queue).elim
  | cons a rest =>
    cases seen : s.seen a with
    | true =>
      simp only [stepCost,queue,seen,if_true,work,advance] at *
      omega
    | false =>
      have unreadDrop := unread_mark buckets s.seen a seen
      have ticks := tickCost_bound s.counter (buckets a)
      have pushes := tick_ready_length s.counter (buckets a)
      simp only [stepCost,queue,seen,Bool.false_eq_true,if_false,work,advance] at *
      omega

theorem cost_bound (buckets : A → List R) (head : R → A) (fuel : Nat) (s : State A R) :
    cost buckets head fuel s ≤ 20*work buckets s+1 := by
  induction fuel generalizing s with
  | zero => simp [cost]
  | succ n ih =>
    by_cases empty : s.queue=[]
    · simp [cost,empty]
    · rw [cost,if_neg empty]
      have later := ih (advance buckets head s)
      have budget := step_budget buckets head s empty
      omega

def totalCost (edges : List (A × R)) (head : R → A) : Nat :=
  2*Fintype.card A+5*Fintype.card R+indexCost edges+
    queueCost (index edges).counter Enumeration.values+
    cost (index edges).bucket head (Fintype.card R) (initial edges head)+1

def inputSize (edges : List (A × R)) : Nat := Fintype.card A+Fintype.card R+edges.length+1

theorem linear_bound (edges : List (A × R)) (head : R → A) : totalCost edges head ≤ 40*inputSize edges := by
  have queued := queueCost_bound (index edges).counter Enumeration.values
  have execution := cost_bound (index edges).bucket head (Fintype.card R) (initial edges head)
  have initialWork : work (index edges).bucket (initial edges head)=Fintype.card R+edges.length := by
    rw [work,initial_potential]
    simp only [unread,initial,initialWithIndex,Bool.false_eq_true,if_false,index_volume]
  rw [initialWork] at execution
  simp only [enumeration_length] at queued
  unfold totalCost inputSize indexCost
  omega

/-- The costed RAM execution follows exactly the state transitions of `run`.
The second component is the operation trace's accumulated charge. -/
def execute (buckets : A → List R) (head : R → A) : Nat → State A R → State A R × Nat
  | 0,s => (s,1)
  | fuel+1,s => if s.queue=[] then (s,1) else
      let later := execute buckets head fuel (advance buckets head s)
      (later.1,stepCost buckets s+later.2)

theorem execute_spec (buckets : A → List R) (head : R → A) (fuel : Nat) (s : State A R) :
    execute buckets head fuel s=(run buckets head fuel s,cost buckets head fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute,run,cost]
    split
    · rfl
    · rw [ih]

/-- Index construction is shared by initialization and propagation. -/
def executeInput (edges : List (A × R)) (head : R → A) : State A R × Nat :=
  let tables := index edges
  let start := initialWithIndex tables head
  let finish := execute tables.bucket head (Fintype.card R) start
  (finish.1,2*Fintype.card A+5*Fintype.card R+indexCost edges+
    queueCost tables.counter Enumeration.values+finish.2+1)

theorem executeInput_spec (edges : List (A × R)) (head : R → A) :
    executeInput edges head=(solve edges head,totalCost edges head) := by
  simp only [executeInput,execute_spec,solve,totalCost,initial]

theorem executeInput_linear (edges : List (A × R)) (head : R → A) :
    (executeInput edges head).2 ≤ 40*inputSize edges := by
  rw [executeInput_spec]
  exact linear_bound edges head

end LeanTrominoes.Horn.Worklist.RAM
