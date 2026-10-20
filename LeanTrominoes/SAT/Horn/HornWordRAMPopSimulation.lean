/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMMark

/-! # Simulation of a complete Horn propagation step -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Slot.heads Slot.edgeRules Slot.seen Slot.buckets Slot.counters Slot.links Slot.stack

def popBound (input : Input) (state : HornState input) : ℕ :=
  match state.queue with
  | [] => 0
  | a::_ => if state.seen a then 8 else 13+20*((Worklist.index (Indexed.edges input.2).reverse).bucket a).length

theorem MachineRep.pop {w B : ℕ} (input : Input) (state : HornState input) (data : Data) (contents : Tables)
    (before : MachineRep input state data contents) (nonempty : state.queue≠[])
    (budget : Worklist.potential state≤ input.2.rules.size)
    (bounded : NaturalData.Bounded B data) (frontier : (Layout.ofInput input).frontier≤ B)
    (width : Fits w (128*B : ℕ)) :
    ∃ result finalContents cost, NaturalData.Exec w popBody data result cost ∧
      cost≤ popBound input state ∧
      MachineRep input (Worklist.stackAdvance (Worklist.index (Indexed.edges input.2).reverse).bucket
        (Indexed.head input.2) state) result finalContents ∧ NaturalData.Bounded B result := by
  cases queue : state.queue with
  | nil => exact (nonempty queue).elim
  | cons a rest =>
    have height : data.1 Reg.top=rest.length+1 := by simpa [queue] using before.top
    have positive : 0< data.1 Reg.top := by omega
    have remaining : rest.length+(Worklist.positive state.counter).card< input.2.rules.size := by
      have limit := budget
      simp only [Worklist.potential,queue,List.length_cons] at limit
      omega
    have room : rest.length< input.2.rules.size := by omega
    have atomBound : atomCode a< input.1+1 := by have h := atomCode_le a; omega
    have source : contents Slot.stack rest.length=atomCode a := by
      have cell := before.stack rest.length (by simp [queue])
      simpa [queue] using cell
    have effect := (Layout.ofInput input).popFront_effects data contents before.realizes before.pointers
      rest.length (atomCode a) height before.one before.zero room atomBound source
    have frontBound := (Layout.ofInput input).popFront_bounded data contents before.realizes before.pointers
      bounded frontier rest.length (atomCode a) height before.one room atomBound source
    have storedRest : StackRep contents rest.reverse := by
      intro i within
      have old := before.stack i (by simp only [queue,List.length_reverse,List.length_cons]; simpa using Nat.lt_succ_of_lt (by simpa using within))
      simpa only [queue,List.reverse_cons,List.getElem_append_left within] using old
    cases seen : state.seen a with
    | true =>
      have value : (pop2 data).1 Reg.value=1 := by rw [effect.2.2.2.2.1,before.seen a,seen]; rfl
      have run := popBody_seen_exec bounded before.one positive before.zero (by omega) width
      refine ⟨pop2 data,contents,8,run,?_,?_,frontBound⟩
      · simp [popBound,queue,seen]
      · simp only [Worklist.stackAdvance,queue,seen,ite_true]
        exact ⟨effect.1,effect.2.1,before.heads,before.buckets,before.counters,before.seen,
          storedRest,effect.2.2.1,effect.2.2.2.2.2.1,effect.2.2.2.2.2.2⟩
    | false =>
      let marked := markedContents contents (atomCode a)
      have mark := (Layout.ofInput input).markState_effects (pop2 data) contents effect.1 effect.2.1
        (atomCode a) effect.2.2.2.1 atomBound
      have oneBound : 1≤ B := by have h := bounded.1 Reg.one; rw [before.one] at h; exact h
      have markedBound : NaturalData.Bounded B (pop5 data) := by
        rw [pop5_eq_mark]
        exact (Layout.ofInput input).markState_bounded (pop2 data) frontBound effect.2.1 oneBound
          (by rw [effect.2.2.2.1]; exact atomBound) frontier
      have tick : TickRep input state.counter rest
          ((Worklist.index (Indexed.edges input.2).reverse).bucket a) (pop5 data) marked := by
        refine ⟨mark.1,mark.2.1,?_,?_,?_,?_,?_,remaining,?_,?_⟩
        · intro r
          simpa [marked,markedContents] using before.heads r
        · rw [pop5_eq_mark,mark.2.2.1]
          simpa [marked,markedContents] using before.buckets a
        · intro r
          simpa [marked,markedContents] using before.counters r
        · simpa [StackRep,marked,markedContents] using storedRest
        · rw [pop5_eq_mark,mark.2.2.2.1,effect.2.2.1]
        · rw [pop5_eq_mark,mark.2.2.2.2.2.1,effect.2.2.2.2.2.1]
        · rw [pop5_eq_mark,mark.2.2.2.2.2.2,effect.2.2.2.2.2.2]
      obtain ⟨result,finalContents,cost,traverse,traversalBound,represented,finalBound,frame⟩ :=
        tick.exec input state.counter rest _ (pop5 data) marked markedBound frontier width
      have fresh : (pop2 data).1 Reg.value=0 := by rw [effect.2.2.2.2.1,before.seen a,seen]; rfl
      have run := popBody_fresh_exec bounded before.one positive before.zero fresh width traverse
      refine ⟨result,finalContents,cost+11,run,?_,?_,finalBound⟩
      · simp only [popBound,queue,seen,Bool.false_eq_true,ite_false]
        omega
      · simp only [Worklist.stackAdvance,queue,seen,Bool.false_eq_true,ite_false]
        refine ⟨represented.realizes,represented.pointers,represented.heads,?_,represented.counters,
          ?_,represented.stored,represented.top,represented.one,represented.zero⟩
        · intro atom
          have immutable (slot : Slot) (counter : slot≠Slot.counters) (stack : slot≠Slot.stack)
              (flag : slot≠Slot.seen) : finalContents slot=contents slot := by
            rw [frame slot counter stack]
            exact Function.update_of_ne flag _ _
          rw [immutable Slot.links (by decide) (by decide) (by decide),
            immutable Slot.edgeRules (by decide) (by decide) (by decide),
            immutable Slot.buckets (by decide) (by decide) (by decide)]
          exact before.buckets atom
        · intro atom
          rw [frame Slot.seen (by decide) (by decide)]
          change Function.update (contents Slot.seen) (atomCode a) 1 (atomCode atom)=
            if Function.update state.seen a true atom then 1 else 0
          by_cases same : atom=a
          · subst atom; simp
          · have codes : atomCode atom≠atomCode a := fun h => same (atomCode_injective h)
            simpa only [Function.update_of_ne same,Function.update_of_ne codes] using before.seen atom

end LeanTrominoes.Horn.WordRAM
