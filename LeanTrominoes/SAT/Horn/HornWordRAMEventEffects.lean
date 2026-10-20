/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMEventBounds

/-! # Representation effects of a physical premise event -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.heads Reg.counters Reg.links Reg.stack Reg.rule Reg.value
  Reg.top Reg.event Reg.scratch Reg.headValue
  Slot.heads Slot.edgeRules Slot.buckets Slot.counters Slot.links Slot.stack

theorem storedCounter_registers (data : Data) :
    (storedCounter data).1=Function.update
      (Function.update data.1 Reg.value (data.1 Reg.value-data.1 Reg.one)) Reg.scratch
      (data.1 Reg.counters+data.1 Reg.rule) := by
  simp [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store]

theorem eventAction_preserves (data : Data) (r : Fin 32)
    (value : r≠Reg.value) (scratch : r≠Reg.scratch)
    (head : r≠Reg.headValue) (top : r≠Reg.top) :
    (eventActionState data).1 r=data.1 r := by
  have stored : (storedCounter data).1 r=data.1 r := by
    rw [storedCounter_registers]
    simp only [Function.update_of_ne value,Function.update_of_ne scratch]
  unfold eventActionState
  split
  · rfl
  · split
    · rw [pushState_registers]
      simpa only [Function.update_of_ne top,Function.update_of_ne scratch,Function.update_of_ne head] using stored
    · exact stored

theorem eventContents_untouched (contents : Tables) (r top : ℕ) (slot : Slot)
    (counter : slot≠Slot.counters) (stack : slot≠Slot.stack) :
    eventContents contents r top slot=contents slot := by
  unfold eventContents
  split
  · rfl
  · split <;> simp only [Function.update_of_ne counter,Function.update_of_ne stack]

theorem eventContents_counters (contents : Tables) (r top : ℕ) :
    eventContents contents r top Slot.counters=
      Function.update (contents Slot.counters) r (contents Slot.counters r-1) := by
  by_cases empty : contents Slot.counters r=0
  · have sub : contents Slot.counters r-1=contents Slot.counters r := by omega
    rw [eventContents,if_pos empty,sub,Function.update_eq_self]
  · unfold eventContents
    simp only [empty,ite_false]
    split <;> simp

theorem eventContents_stack (contents : Tables) (r top : ℕ) :
    eventContents contents r top Slot.stack=
      if contents Slot.counters r=1 then
        Function.update (contents Slot.stack) top (contents Slot.heads r) else contents Slot.stack := by
  by_cases empty : contents Slot.counters r=0
  · simp [eventContents,empty]
  · unfold eventContents
    simp only [empty,ite_false]
    split <;> simp_all

/-- The event pointer itself is unchanged until the final link load. -/
theorem event2_controls (data : Data) :
    (event2 data).1 Reg.event=data.1 Reg.event-data.1 Reg.one ∧
    (event2 data).1 Reg.top=data.1 Reg.top ∧ (event2 data).1 Reg.one=data.1 Reg.one ∧
    (event2 data).1 Reg.zero=data.1 Reg.zero := by
  simp [event2,event1,event0,readState,NaturalData.set]

theorem eventAction_top (data : Data) (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0) :
    (eventActionState data).1 Reg.top=
      if data.1 Reg.value=1 then data.1 Reg.top+1 else data.1 Reg.top := by
  have storedValue : (storedCounter data).1 Reg.value=data.1 Reg.value-1 := by
    simp [storedCounter_registers,unit]
  have storedZero : (storedCounter data).1 Reg.zero=0 := by
    simpa [storedCounter_registers] using zero
  have storedTop : (storedCounter data).1 Reg.top=data.1 Reg.top := by simp [storedCounter_registers]
  have storedOne : (storedCounter data).1 Reg.one=1 := by simpa [storedCounter_registers] using unit
  unfold eventActionState
  split
  · rename_i empty
    have valueZero : data.1 Reg.value=0 := empty.trans zero
    simp [valueZero]
  · rename_i nonempty
    split
    · rename_i ready
      have valueOne : data.1 Reg.value=1 := by rw [storedValue,storedZero] at ready; rw [zero] at nonempty; omega
      simp [pushState_registers,storedTop,storedOne,valueOne]
    · rename_i waiting
      have valueNotOne : data.1 Reg.value≠1 := by rw [storedValue,storedZero] at waiting; omega
      simp only [storedTop,valueNotOne,ite_false]

/-- The concrete event instructions follow the stored link and implement one
counter/stack update. The link and immutable tables survive both stores. -/
theorem Layout.eventState_realizes (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (node r top : ℕ) (event : data.1 Reg.event=node+1) (height : data.1 Reg.top=top)
    (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0)
    (nodeBound : node<layout.events) (ruleBound : r<layout.rules) (room : top<layout.rules)
    (source : contents Slot.edgeRules node=r) :
    layout.Realizes (eventState data).2 (eventContents contents r top) ∧
      layout.Pointers (eventState data) ∧ (eventState data).1 Reg.event=contents Slot.links node := by
  have frontPointers : layout.Pointers (event2 data) := by
    apply layout.readState_pointers _ _ Reg.value Reg.counters Reg.rule (scalarRegister_of_large _ (by decide))
    apply layout.readState_pointers _ _ Reg.rule Reg.edgeRules Reg.event (scalarRegister_of_large _ (by decide))
    exact layout.set_pointers data pointers Reg.event (scalarRegister_of_large _ (by decide)) _
  have edgePointer : data.1 Reg.edgeRules=layout.base Slot.edgeRules := pointers Slot.edgeRules
  have counterPointer : data.1 Reg.counters=layout.base Slot.counters := pointers Slot.counters
  have frontRule : (event2 data).1 Reg.rule=r := by
    simp [event2,event1,event0,readState,NaturalData.set,event,unit,edgePointer,
      before Slot.edgeRules node nodeBound,source,Reg.edgeRules]
  have frontValue : (event2 data).1 Reg.value=contents Slot.counters r := by
    have first : (event1 data).1 Reg.rule=r := by
      simpa [event2,readState,NaturalData.set] using frontRule
    have pointer : (event1 data).1 Reg.counters=layout.base Slot.counters := by
      simpa [event1,event0,readState,NaturalData.set,Reg.edgeRules] using counterPointer
    simp only [event2,readState,NaturalData.set,Function.update_self,first,pointer]
    exact before Slot.counters r ruleBound
  have control := event2_controls data
  have action := layout.eventAction_realizes (event2 data) contents before frontPointers
    r top frontRule (control.2.1.trans height) frontValue (control.2.2.1.trans unit)
    (control.2.2.2.trans zero) ruleBound room
  have actionPointers : layout.Pointers (event3 data) := eventAction_pointers layout _ frontPointers
  have actionIndex : (event3 data).1 Reg.event=node := by
    have preserved := eventAction_preserves (event2 data) Reg.event (by decide) (by decide) (by decide) (by decide)
    change (eventActionState (event2 data)).1 Reg.event=node
    rw [preserved,control.1,event,unit]
    omega
  refine ⟨action,layout.readState_pointers _ actionPointers Reg.event Reg.links Reg.event
    (scalarRegister_of_large _ (by decide)),?_⟩
  have read := layout.readState_value (event3 data) (eventContents contents r top) action actionPointers
    Slot.links node nodeBound Reg.event Reg.event actionIndex
  have untouched := eventContents_untouched contents r top Slot.links (by decide) (by decide)
  simpa only [eventState,show pointer Slot.links=Reg.links from rfl,untouched] using read

end LeanTrominoes.Horn.WordRAM
