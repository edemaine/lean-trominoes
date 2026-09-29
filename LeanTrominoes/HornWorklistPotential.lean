/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornWorklistCounters

/-! # Accounting for each Horn rule's unique firing -/
namespace LeanTrominoes.Horn.Worklist
variable {I : Type*} [Fintype I] [DecidableEq I]

def positive (c : I → Nat) : Finset I := Finset.univ.filter (fun r => 0<c r)

theorem tick_balance (c : I → Nat) (events : List I) :
    (positive (tick c events).1).card+(tick c events).2.length=(positive c).card := by
  have split : positive c=positive (tick c events).1 ∪ (tick c events).2.toFinset := by
    ext r
    simp only [positive,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,List.mem_toFinset,
      tick_ready_mem,tick_counter]
    omega
  have disjoint : Disjoint (positive (tick c events).1) (tick c events).2.toFinset := by
    apply Finset.disjoint_left.mpr
    intro r hr ready
    have pos : 0<(tick c events).1 r := (Finset.mem_filter.mp hr).2
    have zero := ((tick_ready_mem c events r).mp (List.mem_toFinset.mp ready)).2
    omega
  rw [split,Finset.card_union_of_disjoint disjoint,List.toFinset_card_of_nodup (tick_ready_nodup c events)]

end LeanTrominoes.Horn.Worklist
