/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMProgram
import LeanTrominoes.Computation.RAM.NaturalArithmetic

/-! # Disjoint endpoint, partner, and path arrays of the matching program -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
abbrev Data := NaturalData 64
abbrev Slot := Fin 7
namespace Slot
abbrev edgeLeft : Slot := 0
abbrev edgeRight : Slot := 1
abbrev partnerLeft : Slot := 2
abbrev partnerRight : Slot := 3
abbrev lengths : Slot := 4
abbrev rowLeft : Slot := 5
abbrev rowRight : Slot := 6
end Slot

structure Layout where
  n : Nat
  m : Nat
  edges : Nat

def Layout.length (a : Layout) (slot : Slot) : Nat :=
  match slot.val with
  | 0 | 1 => a.edges
  | 2 | 4 => a.n
  | 3 => a.m
  | _ => a.n*a.n

def Layout.base (a : Layout) (slot : Slot) : Nat :=
  let afterInput := 4+2*a.edges
  match slot.val with
  | 0 => 4
  | 1 => 4+a.edges
  | 2 => afterInput
  | 3 => afterInput+a.n
  | 4 => afterInput+a.n+a.m
  | 5 => afterInput+2*a.n+a.m
  | _ => afterInput+2*a.n+a.m+a.n*a.n

def Layout.frontier (a : Layout) := 4+2*a.edges+2*a.n+a.m+2*(a.n*a.n)
def pointer (slot : Slot) : Fin 64 := ⟨9+slot.val,by omega⟩
def Layout.ofInput (input : Input) : Layout := ⟨input.1,input.2.1,input.2.2.length⟩

def Layout.Realizes (a : Layout) (memory : Nat → Nat) (contents : Slot → Nat → Nat) : Prop :=
  ∀ slot i, i<a.length slot → memory (a.base slot+i)=contents slot i

def Layout.Pointers (a : Layout) (data : Data) : Prop := ∀ slot, data.1 (pointer slot)=a.base slot

theorem Layout.disjoint (a : Layout) (s t : Slot) (different : s≠t)
    (i j : Nat) (hi : i<a.length s) (hj : j<a.length t) : a.base s+i≠a.base t+j := by
  fin_cases s <;> fin_cases t <;> simp_all [Layout.base,Layout.length] <;> omega

theorem Layout.address_bound (a : Layout) (slot : Slot) (i : Nat) (within : i<a.length slot) :
    a.base slot+i<a.frontier := by
  fin_cases slot <;> simp_all [Layout.base,Layout.length,Layout.frontier] <;> omega

theorem Layout.write_realizes (a : Layout) (memory : Nat → Nat) (contents : Slot → Nat → Nat)
    (before : a.Realizes memory contents) (slot : Slot) (i value : Nat) (within : i<a.length slot) :
    a.Realizes (Function.update memory (a.base slot+i) value)
      (Function.update contents slot (Function.update (contents slot) i value)) := by
  intro other j hj
  by_cases same : other=slot
  · subst other
    by_cases equal : j=i
    · subst j; simp
    · have different : a.base slot+j≠a.base slot+i := by omega
      simp only [Function.update_of_ne different,Function.update_self,Function.update_of_ne equal]
      exact before slot j hj
  · rw [Function.update_of_ne (a.disjoint other slot same j i hj within),Function.update_of_ne same]
    exact before other j hj

def readState (data : Data) (base index dst : Fin 64) : Data :=
  (data.set Reg.scratch (data.1 base+data.1 index)).set dst (data.2 (data.1 base+data.1 index))
def writeState (data : Data) (base index value : Fin 64) : Data :=
  (data.set Reg.scratch (data.1 base+data.1 index)).store (data.1 base+data.1 index) (data.1 value)

theorem readState_exec {w : Nat} (data : Data) (base index dst : Fin 64)
    (addressFits : Fits w (data.1 base+data.1 index : Nat))
    (valueFits : Fits w (data.2 (data.1 base+data.1 index))) :
    NaturalData.Exec w (read base index dst) data (readState data base index dst) 2 :=
  NaturalData.read_exec data Reg.scratch dst base index addressFits valueFits

theorem writeState_exec {w : Nat} (data : Data) (base index value : Fin 64) (different : value≠Reg.scratch)
    (addressFits : Fits w (data.1 base+data.1 index : Nat)) (valueFits : Fits w (data.1 value)) :
    NaturalData.Exec w (write base index value) data (writeState data base index value) 2 :=
  NaturalData.write_exec data Reg.scratch value base index different addressFits valueFits

def ScalarRegister (i : Fin 64) : Prop := ∀ slot, i≠pointer slot

theorem scalarRegister_of_large (i : Fin 64) (large : 16 ≤ i.val) : ScalarRegister i := by
  intro slot same
  have h := congrArg Fin.val same
  simp only [pointer] at h
  have := slot.isLt
  omega

theorem Layout.set_pointers (a : Layout) (data : Data) (before : a.Pointers data)
    (i : Fin 64) (safe : ScalarRegister i) (value : Nat) : a.Pointers (data.set i value) := by
  intro slot
  simpa [NaturalData.set,Ne.symm (safe slot)] using before slot

theorem Layout.readState_pointers (a : Layout) (data : Data) (before : a.Pointers data)
    (base index dst : Fin 64) (safe : ScalarRegister dst) : a.Pointers (readState data base index dst) :=
  a.set_pointers _ (a.set_pointers data before Reg.scratch (scalarRegister_of_large _ (by decide)) _) dst safe _

theorem Layout.writeState_pointers (a : Layout) (data : Data) (before : a.Pointers data)
    (base index value : Fin 64) : a.Pointers (writeState data base index value) :=
  a.set_pointers data before Reg.scratch (scalarRegister_of_large _ (by decide)) _

theorem Layout.readState_value (a : Layout) (data : Data) (contents : Slot → Nat → Nat)
    (before : a.Realizes data.2 contents) (pointers : a.Pointers data) (slot : Slot) (i : Nat)
    (within : i<a.length slot) (dst index : Fin 64) (idx : data.1 index=i) :
    (readState data (pointer slot) index dst).1 dst=contents slot i := by
  simp only [readState,NaturalData.set,Function.update_self,pointers slot,idx]
  exact before slot i within

theorem Layout.writeState_realizes (a : Layout) (data : Data) (contents : Slot → Nat → Nat)
    (before : a.Realizes data.2 contents) (pointers : a.Pointers data) (slot : Slot) (i : Nat)
    (within : i<a.length slot) (value index : Fin 64) (idx : data.1 index=i) :
    a.Realizes (writeState data (pointer slot) index value).2
      (Function.update contents slot (Function.update (contents slot) i (data.1 value))) := by
  simpa only [writeState,NaturalData.set,NaturalData.store,pointers slot,idx] using
    a.write_realizes data.2 contents before slot i (data.1 value) within

end LeanTrominoes.BipartiteMatching.DenseWordRAM
