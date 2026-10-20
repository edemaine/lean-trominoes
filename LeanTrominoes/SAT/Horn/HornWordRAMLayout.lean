/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMInput

/-! # The allocated arrays in the Horn program's invariant

The input uses three arrays, and the program allocates five more. Blocks occur
in allocation order, so all address-disjointness arguments reduce to bounds on
array indices. This is proof data for the concrete program, not a RAM primitive.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

abbrev Slot := Fin 8
namespace Slot
abbrev heads : Slot := 0
abbrev edgeAtoms : Slot := 1
abbrev edgeRules : Slot := 2
abbrev seen : Slot := 3
abbrev buckets : Slot := 4
abbrev counters : Slot := 5
abbrev links : Slot := 6
abbrev stack : Slot := 7
end Slot

structure Layout where
  numVars : ℕ
  rules : ℕ
  events : ℕ

def Layout.length (layout : Layout) (slot : Slot) : ℕ :=
  match slot.val with
  | 0 => layout.rules
  | 1 | 2 | 6 => layout.events
  | 3 | 4 => layout.numVars+1
  | _ => layout.rules

def Layout.base (layout : Layout) (slot : Slot) : ℕ :=
  let inputEnd := 4+layout.rules+2*layout.events
  let atoms := layout.numVars+1
  match slot.val with
  | 0 => 4
  | 1 => 4+layout.rules
  | 2 => 4+layout.rules+layout.events
  | 3 => inputEnd
  | 4 => inputEnd+atoms
  | 5 => inputEnd+2*atoms
  | 6 => inputEnd+2*atoms+layout.rules
  | _ => inputEnd+2*atoms+layout.rules+layout.events

def Layout.block (layout : Layout) (slot : Slot) : Allocation.Block :=
  ⟨layout.base slot,layout.length slot⟩

def Layout.frontier (layout : Layout) : ℕ := layout.base Slot.stack+layout.rules

def Layout.ofInput (input : Input) : Layout :=
  ⟨input.1,input.2.rules.size,(Indexed.edges input.2).length⟩

def pointer (slot : Slot) : Fin 32 := ⟨9+slot.val,by omega⟩

/-- An array contents function has no operational cost: `Realizes` relates it
to actual memory cells. All program accesses remain ordinary loads and stores. -/
def Layout.Realizes (layout : Layout) (memory : ℕ → ℕ) (contents : Slot → ℕ → ℕ) : Prop :=
  ∀ slot index, index<layout.length slot → memory (layout.base slot+index)=contents slot index

def Layout.Pointers (layout : Layout) (data : Data) : Prop :=
  ∀ slot, data.1 (pointer slot)=layout.base slot

theorem Layout.disjoint (layout : Layout) (s t : Slot) (different : s≠t)
    (i j : ℕ) (hi : i<layout.length s) (hj : j<layout.length t) :
    layout.base s+i≠layout.base t+j := by
  fin_cases s <;> fin_cases t <;>
    simp_all [Layout.base,Layout.length] <;> omega

theorem Layout.address_bound (layout : Layout) (slot : Slot) (i : ℕ)
    (hi : i<layout.length slot) : layout.base slot+i<layout.frontier := by
  fin_cases slot <;> simp_all [Layout.base,Layout.length,Layout.frontier,Slot.stack] <;> omega

theorem Layout.frontier_eq (input : Input) :
    (Layout.ofInput input).frontier=preparedBound input := by
  simp [Layout.ofInput,Layout.frontier,Layout.base,Slot.stack,preparedBound,prepareEnd,words_length]
  omega

/-- A store changes exactly one logical element of one array. -/
theorem Layout.write_realizes (layout : Layout) (memory : ℕ → ℕ) (contents : Slot → ℕ → ℕ)
    (before : layout.Realizes memory contents) (slot : Slot) (i value : ℕ) (within : i<layout.length slot) :
    layout.Realizes (Function.update memory (layout.base slot+i) value)
      (Function.update contents slot (Function.update (contents slot) i value)) := by
  intro other j hj
  by_cases same : other=slot
  · subst other
    by_cases eq : j=i
    · subst j; simp
    · have different : layout.base slot+j≠layout.base slot+i := by omega
      simp only [Function.update_of_ne different,Function.update_self,Function.update_of_ne eq]
      exact before slot j hj
  · rw [Function.update_of_ne (layout.disjoint other slot same j i hj within),Function.update_of_ne same]
    exact before other j hj

def ScalarRegister (i : Fin 32) : Prop := ∀ slot, i≠pointer slot

theorem scalarRegister_of_large (i : Fin 32) (large : 17 ≤ i.val) : ScalarRegister i := by
  intro slot same
  have h := congrArg Fin.val same
  simp only [pointer] at h
  have := slot.isLt
  omega

theorem Layout.set_pointers (layout : Layout) (data : Data) (before : layout.Pointers data)
    (i : Fin 32) (safe : ScalarRegister i) (value : ℕ) : layout.Pointers (data.set i value) := by
  intro slot
  simpa [NaturalData.set,Ne.symm (safe slot)] using before slot

theorem Layout.readState_pointers (layout : Layout) (data : Data) (before : layout.Pointers data)
    (dst ptr index : Fin 32) (safe : ScalarRegister dst) :
    layout.Pointers (readState data dst ptr index) :=
  layout.set_pointers _ (layout.set_pointers data before Reg.scratch
    (scalarRegister_of_large _ (by decide)) _) dst safe _

theorem Layout.writeState_pointers (layout : Layout) (data : Data) (before : layout.Pointers data)
    (src ptr index : Fin 32) : layout.Pointers (writeState data src ptr index) := by
  exact layout.set_pointers data before Reg.scratch (scalarRegister_of_large _ (by decide)) _

theorem Layout.readState_value (layout : Layout) (data : Data) (contents : Slot → ℕ → ℕ)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (slot : Slot) (i : ℕ) (within : i<layout.length slot) (dst index : Fin 32)
    (idx : data.1 index=i) : (readState data dst (pointer slot) index).1 dst=contents slot i := by
  simp only [readState,NaturalData.set,Function.update_self,pointers slot,idx]
  exact before slot i within

theorem Layout.writeState_realizes (layout : Layout) (data : Data) (contents : Slot → ℕ → ℕ)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (slot : Slot) (i : ℕ) (within : i<layout.length slot) (src index : Fin 32)
    (idx : data.1 index=i) :
    layout.Realizes (writeState data src (pointer slot) index).2
      (Function.update contents slot (Function.update (contents slot) i (data.1 src))) := by
  simpa only [writeState,NaturalData.set,NaturalData.store,pointers slot,idx] using
    layout.write_realizes data.2 contents before slot i (data.1 src) within

theorem Layout.read_fits {w : ℕ} (layout : Layout) (data : Data) (contents : Slot → ℕ → ℕ)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (slot : Slot) (i : ℕ) (within : i<layout.length slot) (index : Fin 32)
    (idx : data.1 index=i) (width : Fits w layout.frontier) (value : Fits w (contents slot i)) :
    ReadFits w data (pointer slot) index := by
  simp only [ReadFits,pointers slot,idx]
  exact ⟨Allocation.nat_fits_le width (layout.address_bound slot i within).le,
    by simpa only [before slot i within] using value⟩

theorem Layout.write_fits {w : ℕ} (layout : Layout) (data : Data) (pointers : layout.Pointers data)
    (slot : Slot) (i : ℕ) (within : i<layout.length slot) (src index : Fin 32)
    (idx : data.1 index=i) (width : Fits w layout.frontier) (value : Fits w (data.1 src)) :
    WriteFits w data src (pointer slot) index := by
  simp only [WriteFits,pointers slot,idx]
  exact ⟨Allocation.nat_fits_le width (layout.address_bound slot i within).le,value⟩

end LeanTrominoes.Horn.WordRAM
