/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMTickInvariant

/-! # One executed premise event simulates one worklist counter transition -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.heads Reg.edgeRules Reg.counters Reg.links Reg.stack
  Reg.rule Reg.value Reg.top Reg.event Reg.scratch Reg.headValue
  Slot.heads Slot.edgeRules Slot.counters Slot.links Slot.stack

theorem TickRep.step (input : Input) (counter : Indexed.RuleId input.2 → ℕ)
    (stack : List (Option (Fin input.1))) (r : Indexed.RuleId input.2)
    (rest : List (Indexed.RuleId input.2)) (data : Data) (contents : Tables)
    (before : TickRep input counter stack (r::rest) data contents) :
    TickRep input (tickCounter input counter r) (tickStack input counter stack r) rest
      (eventState data) (eventContents contents r.val stack.length) := by
  obtain ⟨node,nodeBound,event,label,tail⟩ := before.chain.uncons
  have room : stack.length< input.2.rules.size := by have cap := before.capacity; omega
  have effect := (Layout.ofInput input).eventState_realizes data contents before.realizes before.pointers
    node r.val stack.length event before.top before.one before.zero nodeBound r.isLt room label
  have control := event2_controls data
  have edgePointer : data.1 Reg.edgeRules=(Layout.ofInput input).base Slot.edgeRules := before.pointers Slot.edgeRules
  have frontRule : (event1 data).1 Reg.rule=r.val := by
    simp [event1,event0,readState,NaturalData.set,event,before.one,edgePointer,
      before.realizes Slot.edgeRules node nodeBound,label]
  have counterPointer : (event1 data).1 Reg.counters=(Layout.ofInput input).base Slot.counters := by
    simpa [event1,event0,readState,NaturalData.set,pointer] using before.pointers Slot.counters
  have frontValue : (event2 data).1 Reg.value=counter r := by
    simp only [event2,readState,NaturalData.set,Function.update_self,frontRule,counterPointer]
    exact (before.realizes Slot.counters r.val r.isLt).trans (before.counters r)
  have nextOne : (eventState data).1 Reg.one=1 := by
    have preserved := eventAction_preserves (event2 data) Reg.one (by decide) (by decide) (by decide) (by decide)
    simpa [eventState,event3,readState,NaturalData.set] using
      preserved.trans (control.2.2.1.trans before.one)
  have nextZero : (eventState data).1 Reg.zero=0 := by
    have preserved := eventAction_preserves (event2 data) Reg.zero (by decide) (by decide) (by decide) (by decide)
    simpa [eventState,event3,readState,NaturalData.set] using
      preserved.trans (control.2.2.2.trans before.zero)
  refine ⟨effect.1,effect.2.1,?_,?_,?_,?_,?_,?_,nextOne,nextZero⟩
  · intro rule
    rw [eventContents_untouched contents r.val stack.length Slot.heads (by decide) (by decide)]
    exact before.heads rule
  · rw [eventContents_untouched contents r.val stack.length Slot.links (by decide) (by decide),
      eventContents_untouched contents r.val stack.length Slot.edgeRules (by decide) (by decide),effect.2.2]
    exact tail
  · intro rule
    rw [eventContents_counters]
    by_cases same : rule=r
    · subst rule
      simp only [Function.update_self,tickCounter,before.counters]
    · have values : rule.val≠r.val := fun h => same (Fin.ext h)
      simpa only [tickCounter,Function.update_of_ne same,Function.update_of_ne values] using before.counters rule
  · intro i within
    rw [eventContents_stack,before.counters r]
    by_cases ready : counter r=1
    · have pushed := before.stored.push contents stack.reverse (Indexed.head input.2 r)
      have withinPush : i<(stack.reverse++[Indexed.head input.2 r]).length := by
        simpa [tickStack,ready] using within
      have cell := pushed i withinPush
      simpa only [Function.update_self,before.heads r,tickStack,ready,ite_true,List.reverse_cons,List.length_reverse]
        using cell
    · simpa only [tickStack,ready,ite_false] using before.stored i (by simpa [tickStack,ready] using within)
  · have actionTop := eventAction_top (event2 data) (control.2.2.1.trans before.one)
      (control.2.2.2.trans before.zero)
    have finalTop : (eventState data).1 Reg.top=(eventActionState (event2 data)).1 Reg.top := by
      simp [eventState,event3,readState,NaturalData.set]
    rw [finalTop,actionTop,frontValue,control.2.1,before.top]
    unfold tickStack
    split <;> simp
  · have balance := tick_balance input counter stack r
    have cap := before.capacity
    omega

end LeanTrominoes.Horn.WordRAM
