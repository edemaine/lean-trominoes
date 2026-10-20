/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMPopArrays

/-! # Marking a fresh Horn atom and loading its bucket -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.seen Reg.buckets Reg.atom Reg.value Reg.top Reg.event Reg.scratch
  Slot.seen Slot.buckets

def markedContents (contents : Tables) (atom : ℕ) :=
  Function.update contents Slot.seen (Function.update (contents Slot.seen) atom 1)

def mark1 (data : Data) := data.set Reg.value 1
def mark2 (data : Data) := writeState (mark1 data) Reg.value Reg.seen Reg.atom
def markState (data : Data) := readState (mark2 data) Reg.event Reg.buckets Reg.atom

theorem pop5_eq_mark (data : Data) : pop5 data=markState (pop2 data) := rfl

theorem Layout.markState_effects (layout : Layout) (data : Data) (contents : Tables)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (atom : ℕ) (value : data.1 Reg.atom=atom) (within : atom<layout.numVars+1) :
    layout.Realizes (markState data).2 (markedContents contents atom) ∧
      layout.Pointers (markState data) ∧ (markState data).1 Reg.event=contents Slot.buckets atom ∧
      (markState data).1 Reg.top=data.1 Reg.top ∧ (markState data).1 Reg.atom=atom ∧
      (markState data).1 Reg.one=data.1 Reg.one ∧ (markState data).1 Reg.zero=data.1 Reg.zero := by
  have p1 : layout.Pointers (mark1 data) := layout.set_pointers data pointers Reg.value
    (scalarRegister_of_large _ (by decide)) _
  have p2 : layout.Pointers (mark2 data) := layout.writeState_pointers _ p1 Reg.value Reg.seen Reg.atom
  have stored : layout.Realizes (mark2 data).2 (markedContents contents atom) := by
    have step := layout.writeState_realizes (mark1 data) contents before p1 Slot.seen atom within
      Reg.value Reg.atom (by simpa [mark1,NaturalData.set] using value)
    simpa [mark2,mark1,markedContents,NaturalData.set,pointer] using step
  refine ⟨stored,layout.readState_pointers (mark2 data) p2 Reg.event Reg.buckets Reg.atom
    (scalarRegister_of_large _ (by decide)),?_,?_,?_,?_,?_⟩
  · have index : (mark2 data).1 Reg.atom=atom := by
      simpa [mark2,mark1,writeState,NaturalData.set,NaturalData.store] using value
    have read := layout.readState_value (mark2 data) (markedContents contents atom) stored p2 Slot.buckets
      atom within Reg.event Reg.atom index
    simpa [markState,markedContents,pointer] using read
  · simp [markState,mark2,mark1,readState,writeState,NaturalData.set,NaturalData.store]
  · simpa [markState,mark2,mark1,readState,writeState,NaturalData.set,NaturalData.store] using value
  · simp [markState,mark2,mark1,readState,writeState,NaturalData.set,NaturalData.store]
  · simp [markState,mark2,mark1,readState,writeState,NaturalData.set,NaturalData.store]

theorem Layout.markState_bounded {B : ℕ} (layout : Layout) (data : Data)
    (before : NaturalData.Bounded B data) (pointers : layout.Pointers data)
    (one : 1≤B) (within : data.1 Reg.atom<layout.numVars+1) (frontier : layout.frontier≤B) :
    NaturalData.Bounded B (markState data) := by
  have b1 : NaturalData.Bounded B (mark1 data) := before.set Reg.value one
  have p1 : layout.Pointers (mark1 data) := layout.set_pointers data pointers Reg.value
    (scalarRegister_of_large _ (by decide)) _
  have b2 : NaturalData.Bounded B (mark2 data) := by
    apply writeState_bounded_same b1
    have ptr : (mark1 data).1 Reg.seen=layout.base Slot.seen := p1 Slot.seen
    have index : (mark1 data).1 Reg.atom=data.1 Reg.atom := by simp [mark1,NaturalData.set]
    rw [ptr,index]
    exact (layout.address_bound Slot.seen _ within).le.trans frontier
  have p2 : layout.Pointers (mark2 data) := layout.writeState_pointers _ p1 Reg.value Reg.seen Reg.atom
  apply readState_bounded_same b2
  have ptr : (mark2 data).1 Reg.buckets=layout.base Slot.buckets := p2 Slot.buckets
  have index : (mark2 data).1 Reg.atom=data.1 Reg.atom := by
    simp [mark2,mark1,writeState,NaturalData.set,NaturalData.store]
  rw [ptr,index]
  exact (layout.address_bound Slot.buckets _ within).le.trans frontier

end LeanTrominoes.Horn.WordRAM
