/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMTickStep

/-! # Bounded-word execution of a whole Horn bucket traversal -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.edgeRules Reg.counters Reg.links Reg.rule Reg.value
  Reg.top Reg.event Reg.scratch Slot.edgeRules Slot.counters Slot.links

theorem TickRep.bounded_step {B : ℕ} (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (r : Indexed.RuleId input.2)
    (rest : List (Indexed.RuleId input.2)) (data : Data) (contents : Tables)
    (before : TickRep input counter stack (r::rest) data contents)
    (bounded : NaturalData.Bounded B data) (frontier : (Layout.ofInput input).frontier≤ B) :
    NaturalData.Bounded B (eventState data) := by
  obtain ⟨node,nodeBound,event,label,tail⟩ := before.chain.uncons
  have controls := event2_controls data
  have room : stack.length< input.2.rules.size := by have cap := before.capacity; omega
  have p0 : (Layout.ofInput input).Pointers (event0 data) :=
    (Layout.ofInput input).set_pointers data before.pointers Reg.event (scalarRegister_of_large _ (by decide)) _
  have p1 : (Layout.ofInput input).Pointers (event1 data) :=
    (Layout.ofInput input).readState_pointers (event0 data) p0 Reg.rule Reg.edgeRules Reg.event
      (scalarRegister_of_large _ (by decide))
  have p2 : (Layout.ofInput input).Pointers (event2 data) :=
    (Layout.ofInput input).readState_pointers (event1 data) p1 Reg.value Reg.counters Reg.rule
      (scalarRegister_of_large _ (by decide))
  have firstIndex : (event0 data).1 Reg.event=node := by simp [event0,NaturalData.set,event,before.one]
  have edgePointer : data.1 Reg.edgeRules=(Layout.ofInput input).base Slot.edgeRules := before.pointers Slot.edgeRules
  have rule : (event1 data).1 Reg.rule=r.val := by
    simp [event1,event0,readState,NaturalData.set,event,before.one,edgePointer,
      before.realizes Slot.edgeRules node nodeBound,label]
  have b0 : NaturalData.Bounded B (event0 data) := bounded.set Reg.event
    ((Nat.sub_le _ _).trans (bounded.1 _))
  have b1 : NaturalData.Bounded B (event1 data) := by
    apply readState_bounded_same b0
    have ptr : (event0 data).1 Reg.edgeRules=(Layout.ofInput input).base Slot.edgeRules := p0 Slot.edgeRules
    rw [ptr,firstIndex]
    exact ((Layout.ofInput input).address_bound Slot.edgeRules node nodeBound).le.trans frontier
  have b2 : NaturalData.Bounded B (event2 data) := by
    apply readState_bounded_same b1
    have ptr : (event1 data).1 Reg.counters=(Layout.ofInput input).base Slot.counters := p1 Slot.counters
    rw [ptr,rule]
    exact ((Layout.ofInput input).address_bound Slot.counters r.val r.isLt).le.trans frontier
  have rule2 : (event2 data).1 Reg.rule=r.val := by simpa [event2,readState,NaturalData.set] using rule
  have b3 : NaturalData.Bounded B (event3 data) :=
    (Layout.ofInput input).eventAction_bounded (event2 data) b2 p2
      (controls.2.2.1.trans before.one) (by simpa only [rule2,Layout.ofInput] using r.isLt)
      (by rw [controls.2.1,before.top]; exact room) frontier
  apply readState_bounded_same b3
  have p3 : (Layout.ofInput input).Pointers (event3 data) := eventAction_pointers _ _ p2
  have ptr : (event3 data).1 Reg.links=(Layout.ofInput input).base Slot.links := p3 Slot.links
  have index : (event3 data).1 Reg.event=node := by
    have preserved := eventAction_preserves (event2 data) Reg.event (by decide) (by decide) (by decide) (by decide)
    change (eventActionState (event2 data)).1 Reg.event=node
    rw [preserved,controls.1,event,before.one]
    omega
  rw [ptr,index]
  exact ((Layout.ofInput input).address_bound Slot.links node nodeBound).le.trans frontier

/-- A whole certified bucket executes on bounded words and agrees with the
verified stack-counter semantics. Every visited node is charged, including
both loop-control instructions. The same word bound holds at the endpoint. -/
theorem TickRep.exec {w B : ℕ} (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (events : List (Indexed.RuleId input.2))
    (data : Data) (contents : Tables) (before : TickRep input counter stack events data contents)
    (bounded : NaturalData.Bounded B data) (frontier : (Layout.ofInput input).frontier≤B)
    (width : Fits w (128*B : ℕ)) :
    ∃ result finalContents cost,
      NaturalData.Exec w processEvents data result cost ∧ cost≤20*events.length+2 ∧
      TickRep input (Worklist.stackTick (Indexed.head input.2) counter events stack).1
        (Worklist.stackTick (Indexed.head input.2) counter events stack).2 [] result finalContents ∧
      NaturalData.Bounded B result ∧
      ∀ slot, slot≠Slot.counters → slot≠Slot.stack → finalContents slot=contents slot := by
  induction events generalizing counter stack data contents with
  | nil =>
    have pointer : data.1 Reg.event=0 := before.chain.zero_iff.mpr rfl
    refine ⟨data,contents,2,?_,by simp,?_,bounded,?_⟩
    · apply Structured.Exec.loop_done
      simp only [Structured.Condition.Holds,NaturalData.word,pointer,before.zero]
      omega
    · simpa only [Worklist.stackTick] using before
    · intros; rfl
  | cons r rest ih =>
    have next := before.step input counter stack r rest data contents
    have nextBound := before.bounded_step input counter stack r rest data contents bounded frontier
    obtain ⟨result,finalContents,cost,traverse,budget,represented,finalBound,frame⟩ :=
      ih (tickCounter input counter r) (tickStack input counter stack r) (eventState data)
        (eventContents contents r.val stack.length) next nextBound
    obtain ⟨node,nodeBound,event,label,tail⟩ := before.chain.uncons
    have body := (eventBody_exec bounded before.one before.zero (by rw [event]; omega) width).1
    refine ⟨result,finalContents,eventBodyCost data+cost+2,?_,?_,?_,finalBound,?_⟩
    · have holds : Structured.Condition.Holds (.lt Reg.zero Reg.event) data.word := by
        simp only [Structured.Condition.Holds,NaturalData.word,before.zero,event]
        omega
      exact Structured.Exec.loop_more holds body traverse
    · have stepBound := eventBodyCost_le data
      simp only [List.length_cons]
      omega
    · simpa only [Worklist.stackTick,tickCounter,tickStack] using represented
    · intro slot counter stack
      exact (frame slot counter stack).trans (eventContents_untouched contents r.val _ slot counter stack)

end LeanTrominoes.Horn.WordRAM
