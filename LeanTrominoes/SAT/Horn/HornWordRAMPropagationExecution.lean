/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMPopSimulation

/-! # Linear bounded-word execution of Horn propagation -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

theorem pop_budget (input : Input) (state : HornState input) (nonempty : state.queue≠[]) :
    popBound input state+2+
      30*Worklist.RAM.work (Worklist.index (Indexed.edges input.2).reverse).bucket
        (Worklist.stackAdvance (Worklist.index (Indexed.edges input.2).reverse).bucket (Indexed.head input.2) state)≤
      30*Worklist.RAM.work (Worklist.index (Indexed.edges input.2).reverse).bucket state := by
  let buckets := (Worklist.index (Indexed.edges input.2).reverse).bucket
  have drop := Worklist.stackAdvance_potential buckets (Indexed.head input.2) state nonempty
  cases queue : state.queue with
  | nil => exact (nonempty queue).elim
  | cons a rest =>
    cases seen : state.seen a with
    | true =>
      have unchanged :
          (Worklist.stackAdvance buckets (Indexed.head input.2) state).seen=state.seen := by
        simp [Worklist.stackAdvance,queue,seen]
      simp only [popBound,queue,seen,ite_true,Worklist.RAM.work]
      change 8+2+30*(Worklist.potential (Worklist.stackAdvance buckets (Indexed.head input.2) state)+
        Worklist.RAM.unread buckets (Worklist.stackAdvance buckets (Indexed.head input.2) state).seen)≤
        30*(Worklist.potential state+Worklist.RAM.unread buckets state.seen)
      rw [unchanged]
      omega
    | false =>
      have unread := Worklist.RAM.unread_mark buckets state.seen a seen
      have marked : (Worklist.stackAdvance buckets (Indexed.head input.2) state).seen=
          Function.update state.seen a true := by simp [Worklist.stackAdvance,queue,seen]
      simp only [popBound,queue,seen,Bool.false_eq_true,ite_false,Worklist.RAM.work]
      change 13+20*(buckets a).length+2+
        30*(Worklist.potential (Worklist.stackAdvance buckets (Indexed.head input.2) state)+
          Worklist.RAM.unread buckets (Worklist.stackAdvance buckets (Indexed.head input.2) state).seen)≤
        30*(Worklist.potential state+Worklist.RAM.unread buckets state.seen)
      rw [marked]
      omega

/-- Propagation follows the verified stack machine and uses a linear
instruction budget. All reached machine words obey the same bound B. -/
theorem MachineRep.propagate {w B : ℕ} (input : Input) (fuel : ℕ)
    (state : HornState input) (data : Data) (contents : Tables)
    (before : MachineRep input state data contents) (enough : Worklist.potential state≤ fuel)
    (budget : Worklist.potential state≤ input.2.rules.size) (bounded : NaturalData.Bounded B data)
    (frontier : (Layout.ofInput input).frontier≤ B) (width : Fits w (128*B : ℕ)) :
    ∃ result finalContents cost, NaturalData.Exec w propagate data result cost ∧
      cost≤30*Worklist.RAM.work (Worklist.index (Indexed.edges input.2).reverse).bucket state+2 ∧
      MachineRep input (Worklist.stackRun (Worklist.index (Indexed.edges input.2).reverse).bucket
        (Indexed.head input.2) fuel state) result finalContents ∧ NaturalData.Bounded B result := by
  induction fuel generalizing state data contents with
  | zero =>
    have empty : state.queue=[] := by
      have length : state.queue.length=0 := by dsimp [Worklist.potential] at enough; omega
      exact List.length_eq_zero_iff.mp length
    refine ⟨data,contents,2,?_,by omega,?_,bounded⟩
    · apply Structured.Exec.loop_done
      simp only [Structured.Condition.Holds,NaturalData.word,before.top,before.zero,empty,List.length_nil]
      omega
    · simpa only [Worklist.stackRun] using before
  | succ fuel ih =>
    by_cases empty : state.queue=[]
    · refine ⟨data,contents,2,?_,by omega,?_,bounded⟩
      · apply Structured.Exec.loop_done
        simp only [Structured.Condition.Holds,NaturalData.word,before.top,before.zero,empty,List.length_nil]
        omega
      · simpa only [Worklist.stackRun,empty,ite_true] using before
    · obtain ⟨middle,middleContents,stepCost,step,stepBound,represented,middleBound⟩ :=
        before.pop input state data contents empty budget bounded frontier width
      have drop := Worklist.stackAdvance_potential
        (Worklist.index (Indexed.edges input.2).reverse).bucket (Indexed.head input.2) state empty
      obtain ⟨result,finalContents,cost,tail,tailBound,finalRep,finalBound⟩ :=
        ih _ middle middleContents represented (by omega) (by omega) middleBound
      refine ⟨result,finalContents,stepCost+cost+2,?_,?_,?_,finalBound⟩
      · apply Structured.Exec.loop_more ?_ step tail
        simp only [Structured.Condition.Holds,NaturalData.word,before.top,before.zero]
        have positive : 0< state.queue.length := List.length_pos_iff.mpr empty
        exact_mod_cast positive
      · have amortized := pop_budget input state empty
        omega
      · simpa only [Worklist.stackRun,empty,ite_false] using finalRep

end LeanTrominoes.Horn.WordRAM
