/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMPop
import LeanTrominoes.SAT.Horn.HornWordRAMTickExecution

/-! # Array effects of popping and marking a Horn work item -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.seen Reg.buckets Reg.stack Reg.atom Reg.value
  Reg.top Reg.event Reg.scratch Slot.seen Slot.buckets Slot.stack

theorem Layout.popFront_effects (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (top atom : ℕ) (height : data.1 Reg.top=top+1) (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0)
    (within : top<layout.rules) (atomBound : atom<layout.numVars+1) (source : contents Slot.stack top=atom) :
    layout.Realizes (pop2 data).2 contents ∧ layout.Pointers (pop2 data) ∧
      (pop2 data).1 Reg.top=top ∧ (pop2 data).1 Reg.atom=atom ∧
      (pop2 data).1 Reg.value=contents Slot.seen atom ∧
      (pop2 data).1 Reg.one=1 ∧ (pop2 data).1 Reg.zero=0 := by
  have stack : data.1 Reg.stack=layout.base Slot.stack := pointers Slot.stack
  have seen : data.1 Reg.seen=layout.base Slot.seen := pointers Slot.seen
  have atomValue : (pop1 data).1 Reg.atom=atom := by
    simp [pop1,pop0,readState,NaturalData.set,stack,height,unit,before Slot.stack top within,source]
  have seenPointer : (pop1 data).1 Reg.seen=layout.base Slot.seen := by
    simpa [pop1,pop0,readState,NaturalData.set] using seen
  have p0 : layout.Pointers (pop0 data) :=
    layout.set_pointers data pointers Reg.top (scalarRegister_of_large _ (by decide)) _
  have p1 : layout.Pointers (pop1 data) := layout.readState_pointers (pop0 data) p0 Reg.atom Reg.stack Reg.top
    (scalarRegister_of_large _ (by decide))
  refine ⟨before,layout.readState_pointers (pop1 data) p1 Reg.value Reg.seen Reg.atom
    (scalarRegister_of_large _ (by decide)),?_,?_,?_,?_,?_⟩
  · simp [pop2,pop1,pop0,readState,NaturalData.set,height,unit]
  · simpa [pop2,readState,NaturalData.set] using atomValue
  · simp only [pop2,readState,NaturalData.set,Function.update_self,atomValue,seenPointer]
    exact before Slot.seen atom atomBound
  · simpa [pop2,pop1,pop0,readState,NaturalData.set] using unit
  · simpa [pop2,pop1,pop0,readState,NaturalData.set] using zero

theorem Layout.popFront_bounded {B : ℕ} (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (bounded : NaturalData.Bounded B data) (frontier : layout.frontier≤B)
    (top atom : ℕ) (height : data.1 Reg.top=top+1) (unit : data.1 Reg.one=1)
    (within : top<layout.rules) (atomBound : atom<layout.numVars+1) (source : contents Slot.stack top=atom) :
    NaturalData.Bounded B (pop2 data) := by
  have p0 : layout.Pointers (pop0 data) := layout.set_pointers data pointers Reg.top
    (scalarRegister_of_large _ (by decide)) _
  have index : (pop0 data).1 Reg.top=top := by simp [pop0,NaturalData.set,height,unit]
  have atomValue : (pop1 data).1 Reg.atom=atom := by
    have ptr : data.1 Reg.stack=layout.base Slot.stack := pointers Slot.stack
    simp [pop1,pop0,readState,NaturalData.set,ptr,height,unit,before Slot.stack top within,source]
  have p1 : layout.Pointers (pop1 data) := layout.readState_pointers (pop0 data) p0 Reg.atom Reg.stack Reg.top
    (scalarRegister_of_large _ (by decide))
  have b0 : NaturalData.Bounded B (pop0 data) := bounded.set Reg.top ((Nat.sub_le _ _).trans (bounded.1 _))
  have b1 : NaturalData.Bounded B (pop1 data) := by
    apply readState_bounded_same b0
    have ptr : (pop0 data).1 Reg.stack=layout.base Slot.stack := p0 Slot.stack
    rw [ptr,index]
    exact (layout.address_bound Slot.stack top within).le.trans frontier
  apply readState_bounded_same b1
  have ptr : (pop1 data).1 Reg.seen=layout.base Slot.seen := p1 Slot.seen
  rw [ptr,atomValue]
  exact (layout.address_bound Slot.seen atom atomBound).le.trans frontier

end LeanTrominoes.Horn.WordRAM
