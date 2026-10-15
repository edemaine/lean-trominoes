/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-! # Counter updates for a Horn occurrence worklist

Each event reads and decrements one indexed counter. A rule is reported exactly
when its counter changes from one to zero, including repeated occurrences.
-/
namespace LeanTrominoes.Horn.Worklist
variable {I : Type*} [DecidableEq I]

def tick (c : I → Nat) : List I → (I → Nat) × List I
  | [] => (c,[])
  | r::rs =>
    let next := tick (Function.update c r (c r-1)) rs
    (next.1,if c r=1 then r::next.2 else next.2)

theorem tick_counter (c : I → Nat) (events : List I) (r : I) :
    (tick c events).1 r = c r-events.count r := by
  induction events generalizing c with
  | nil => simp [tick]
  | cons a events ih =>
    simp only [tick,ih]
    by_cases h : r=a
    · subst a
      simp [List.count_cons,Function.update_self,Nat.sub_sub]
      omega
    · simp [List.count_cons,h,Ne.symm h,Function.update_of_ne h]

theorem tick_ready_count (c : I → Nat) (events : List I) (r : I) :
    (tick c events).2.count r = if 0<c r ∧ c r≤events.count r then 1 else 0 := by
  induction events generalizing c with
  | nil => simp [tick]; omega
  | cons a events ih =>
    by_cases same : r=a
    · subst a
      by_cases one : c r=1
      · simp [tick,one,ih]
      · simp only [tick,if_neg one,ih,Function.update_self]
        simp only [List.count_cons_self]
        split <;> split <;> omega
    · by_cases one : c a=1
      · simp [tick,one,List.count_cons,same,Ne.symm same,ih,Function.update_of_ne same]
      · simp [tick,one,List.count_cons,same,Ne.symm same,ih,Function.update_of_ne same]

theorem tick_ready_mem (c : I → Nat) (events : List I) (r : I) :
    r ∈ (tick c events).2 ↔ 0<c r ∧ (tick c events).1 r=0 := by
  rw [← List.count_pos_iff,tick_ready_count,tick_counter]
  split <;> simp_all <;> omega

theorem tick_ready_nodup (c : I → Nat) (events : List I) : (tick c events).2.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro r
  rw [tick_ready_count]
  split <;> omega

theorem tick_ready_length (c : I → Nat) (events : List I) : (tick c events).2.length ≤ events.length := by
  induction events generalizing c with
  | nil => simp [tick]
  | cons r events ih =>
    simp only [tick,List.length_cons]
    split <;> (try simp only [List.length_cons])
    all_goals have bound := ih (Function.update c r (c r-1)); omega

end LeanTrominoes.Horn.Worklist
