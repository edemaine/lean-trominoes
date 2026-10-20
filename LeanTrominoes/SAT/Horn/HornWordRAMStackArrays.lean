/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStackInput

/-! # Physical stack updates in the Horn RAM program -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.rules Reg.heads Reg.counters Reg.stack Reg.index
  Reg.rule Reg.value Reg.top Reg.scratch Reg.headValue
  Slot.heads Slot.edgeAtoms Slot.edgeRules Slot.seen Slot.buckets Slot.counters Slot.links Slot.stack

theorem pushState_pointers (layout : Layout) (data : Data) (before : layout.Pointers data) :
    layout.Pointers (pushState data) := by
  apply layout.set_pointers _ _ Reg.top (scalarRegister_of_large _ (by decide))
  apply layout.writeState_pointers
  exact layout.readState_pointers data before Reg.headValue Reg.heads Reg.rule
    (scalarRegister_of_large _ (by decide))

theorem stackBody_pointers (layout : Layout) (data : Data) (before : layout.Pointers data) :
    layout.Pointers (stackBodyState data) := by
  apply layout.set_pointers _ _ Reg.index (scalarRegister_of_large _ (by decide))
  have loaded : layout.Pointers (stackRead data) :=
    layout.readState_pointers data before Reg.value Reg.counters Reg.index
      (scalarRegister_of_large _ (by decide))
  unfold stackBranch
  split
  · exact pushState_pointers layout _
      (layout.set_pointers _ loaded Reg.rule (scalarRegister_of_large _ (by decide)) _)
  · exact loaded

theorem stackBody_memory (data : Data) :
    (stackBodyState data).2=
      if data.2 (data.1 Reg.counters+data.1 Reg.index)=data.1 Reg.zero then
        Function.update data.2 (data.1 Reg.stack+data.1 Reg.top)
          (data.2 (data.1 Reg.heads+data.1 Reg.index)) else data.2 := by
  unfold stackBodyState stackBranch
  split <;> simp_all [stackRead,readState,pushState_memory,NaturalData.set]

theorem stackBody_top (data : Data) :
    (stackBodyState data).1 Reg.top=
      if data.2 (data.1 Reg.counters+data.1 Reg.index)=data.1 Reg.zero then
        data.1 Reg.top+data.1 Reg.one else data.1 Reg.top := by
  unfold stackBodyState stackBranch
  split <;> simp_all [stackRead,readState,pushState_registers,NaturalData.set]

def stackContents (contents : Tables) (index top : ℕ) : Tables :=
  if contents Slot.counters index=0 then
    Function.update contents Slot.stack (Function.update (contents Slot.stack) top (contents Slot.heads index))
  else contents

/-- A scan iteration reads the intended rule counter and, precisely when it
is zero, appends the intended head to the allocated stack. -/
theorem Layout.stackBody_realizes (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (index top : ℕ) (idx : data.1 Reg.index=index) (height : data.1 Reg.top=top)
    (zero : data.1 Reg.zero=0) (within : index<layout.rules) (room : top<layout.rules) :
    layout.Realizes (stackBodyState data).2 (stackContents contents index top) := by
  have counter := before Slot.counters index within
  have head := before Slot.heads index within
  rw [stackBody_memory]
  have pc : data.1 Reg.counters=layout.base Slot.counters := pointers Slot.counters
  have ph : data.1 Reg.heads=layout.base Slot.heads := pointers Slot.heads
  have ps : data.1 Reg.stack=layout.base Slot.stack := pointers Slot.stack
  rw [pc,ph,ps,idx,height,zero,counter,head]
  unfold stackContents
  split
  · exact layout.write_realizes data.2 contents before Slot.stack top (contents Slot.heads index) room
  · exact before

/-- The list is stored from bottom to top; propagation reads its last entry. -/
def StackRep {n : ℕ} (contents : Tables) (entries : List (Option (Fin n))) : Prop :=
  ∀ i, (within : i<entries.length) → contents Slot.stack i=atomCode entries[i]

theorem StackRep.empty {n : ℕ} (contents : Tables) : StackRep (n := n) contents [] := by
  intro i within
  simp at within

theorem StackRep.push {n : ℕ} (contents : Tables) (entries : List (Option (Fin n)))
    (before : StackRep contents entries) (head : Option (Fin n)) :
    StackRep (Function.update contents Slot.stack
      (Function.update (contents Slot.stack) entries.length (atomCode head))) (entries++[head]) := by
  intro i within
  simp only [Function.update_self]
  by_cases old : i<entries.length
  · have different : i≠entries.length := by omega
    rw [Function.update_of_ne different,List.getElem_append_left old]
    exact before i old
  · have last : i=entries.length := by simp only [List.length_append,List.length_singleton] at within; omega
    subst i
    simp

end LeanTrominoes.Horn.WordRAM
