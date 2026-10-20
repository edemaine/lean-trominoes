/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMEvents

/-! # Logical effects of the checked event instructions -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.heads Reg.counters Reg.stack Reg.rule Reg.value
  Reg.top Reg.scratch Reg.headValue
  Slot.heads Slot.edgeRules Slot.buckets Slot.counters Slot.links Slot.stack

theorem Layout.pushState_realizes (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (r top : ℕ) (rule : data.1 Reg.rule=r) (height : data.1 Reg.top=top)
    (within : r<layout.rules) (room : top<layout.rules) :
    layout.Realizes (pushState data).2
      (Function.update contents Slot.stack (Function.update (contents Slot.stack) top (contents Slot.heads r))) := by
  rw [pushState_memory]
  have heads : data.1 Reg.heads=layout.base Slot.heads := pointers Slot.heads
  have stack : data.1 Reg.stack=layout.base Slot.stack := pointers Slot.stack
  rw [heads,stack,rule,height,before Slot.heads r within]
  exact layout.write_realizes data.2 contents before Slot.stack top (contents Slot.heads r) room

def eventContents (contents : Tables) (r top : ℕ) : Tables :=
  if contents Slot.counters r=0 then contents else
    let lowered := Function.update contents Slot.counters
      (Function.update (contents Slot.counters) r (contents Slot.counters r-1))
    if contents Slot.counters r=1 then
      Function.update lowered Slot.stack
        (Function.update (lowered Slot.stack) top (contents Slot.heads r))
    else lowered

theorem storedCounter_pointers (layout : Layout) (data : Data) (before : layout.Pointers data) :
    layout.Pointers (storedCounter data) :=
  layout.writeState_pointers _
    (layout.set_pointers data before Reg.value (scalarRegister_of_large _ (by decide)) _) _ _ _

theorem eventAction_pointers (layout : Layout) (data : Data) (before : layout.Pointers data) :
    layout.Pointers (eventActionState data) := by
  unfold eventActionState
  split
  · exact before
  · split
    · exact pushState_pointers layout _ (storedCounter_pointers layout data before)
    · exact storedCounter_pointers layout data before

/-- Counter decrement and optional head push use the same physical state as
the instruction certificate. Every unrelated array cell is preserved. -/
theorem Layout.eventAction_realizes (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (r top : ℕ) (rule : data.1 Reg.rule=r) (height : data.1 Reg.top=top)
    (value : data.1 Reg.value=contents Slot.counters r)
    (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0)
    (within : r<layout.rules) (room : top<layout.rules) :
    layout.Realizes (eventActionState data).2 (eventContents contents r top) := by
  let lowered := Function.update contents Slot.counters
    (Function.update (contents Slot.counters) r (contents Slot.counters r-1))
  have lowPointers : layout.Pointers (loweredCounter data) :=
    layout.set_pointers data pointers Reg.value (scalarRegister_of_large _ (by decide)) _
  have stored : layout.Realizes (storedCounter data).2 lowered := by
    have step := layout.writeState_realizes (loweredCounter data) contents before lowPointers
      Slot.counters r within Reg.value Reg.rule (by simpa [loweredCounter,NaturalData.set] using rule)
    simpa [storedCounter,loweredCounter,NaturalData.set,lowered,pointer,value,unit] using step
  have nextValue : (storedCounter data).1 Reg.value=contents Slot.counters r-1 := by
    simp [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store,value,unit]
  have nextZero : (storedCounter data).1 Reg.zero=0 := by
    simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using zero
  have nextRule : (storedCounter data).1 Reg.rule=r := by
    simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using rule
  have nextTop : (storedCounter data).1 Reg.top=top := by
    simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using height
  unfold eventActionState eventContents
  rw [value,zero,nextValue,nextZero]
  by_cases empty : contents Slot.counters r=0
  · simp only [empty,ite_true]
    exact before
  · simp only [empty,ite_false]
    by_cases ready : contents Slot.counters r=1
    · have sub : contents Slot.counters r-1=0 := by omega
      rw [if_pos ready,if_pos sub]
      have pushed := layout.pushState_realizes (storedCounter data) lowered stored
        (storedCounter_pointers layout data pointers) r top nextRule nextTop within room
      simpa only [lowered,Function.update_of_ne (show Slot.heads≠Slot.counters by decide)] using pushed
    · have sub : contents Slot.counters r-1≠0 := by omega
      rw [if_neg ready,if_neg sub]
      exact stored

end LeanTrominoes.Horn.WordRAM
