/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripPacked

/-! # Natural-number placement records for the strip transition evaluator -/

namespace LeanTrominoes.PolyominoStripWindow.Raw

abbrev Slot := Bool × SquareSymmetry × Nat
abbrev Candidate := Nat × Slot

def slots (height bound : Nat) : List Slot :=
  [false,true].flatMap fun kind => symmetries.flatMap fun symmetry =>
    (List.range (height+2*bound+1)).map fun y => (kind,symmetry,y)

def keys (height bound : Nat) : List Candidate :=
  (List.range (2*bound+1)).flatMap fun column =>
    (slots height bound).map fun slot => (column,slot)

def eraseSlot {height bound : Nat} (slot : PolyominoStripWindow.Slot Bool height bound) : Slot :=
  (slot.1,slot.2.1,slot.2.2.val)

def erase {height bound : Nat} (a : PolyominoStripWindow.Candidate Bool height bound) : Candidate :=
  (a.1.val,eraseSlot a.2)

theorem eraseSlot_injective {height bound : Nat} :
    Function.Injective (@eraseSlot height bound) := by
  rintro ⟨k,s,y⟩ ⟨l,t,z⟩ h
  simp only [eraseSlot,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,h⟩
  have : y = z := Fin.ext h
  subst z
  rfl

theorem erase_injective {height bound : Nat} :
    Function.Injective (@erase height bound) := by
  intro a b h
  have hc : a.1 = b.1 := Fin.ext (congrArg Prod.fst h)
  have hs : a.2 = b.2 := eraseSlot_injective (congrArg Prod.snd h)
  exact Prod.ext hc hs

@[simp] theorem mem_slots {height bound : Nat} (slot : Slot) :
    slot ∈ slots height bound ↔ slot.2.2 < height+2*bound+1 := by
  rcases slot with ⟨k,s,y⟩
  cases k <;> simp [slots,mem_symmetries]

@[simp] theorem mem_keys {height bound : Nat} (a : Candidate) :
    a ∈ keys height bound ↔ a.1 < 2*bound+1 ∧ a.2.2.2 < height+2*bound+1 := by
  rcases a with ⟨column,slot⟩
  simp only [keys,List.mem_flatMap,List.mem_map,Prod.mk.injEq,
    List.mem_range,mem_slots]
  constructor
  · rintro ⟨a,ha,b,hb,rfl,rfl⟩; exact ⟨ha,hb⟩
  · rintro ⟨ha,hb⟩; exact ⟨column,ha,slot,hb,rfl,rfl⟩

private theorem map_finRange_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Erasing proofs preserves the exact bit order of the semantic encoding. -/
theorem map_erase_keys (height bound : Nat) :
    (PolyominoStripWindow.keys height bound).map erase = keys height bound := by
  simp only [PolyominoStripWindow.keys,keys,slots,List.map_flatMap,List.map_map]
  rw [← map_finRange_val (2*bound+1)]
  simp only [List.flatMap_map]
  congr 1
  funext column
  congr 1
  funext kind
  congr 1
  funext symmetry
  rw [← map_finRange_val (height+2*bound+1)]
  simp only [List.map_map,Function.comp_def,erase,eraseSlot]

private theorem idxOf_map_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) (xs : List α) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases h : b = a
    · subst b; simp
    · have h' : f b ≠ f a := fun eq => h (hf eq)
      simp [List.idxOf_cons_ne xs h,List.idxOf_cons_ne (xs.map f) h',ih]

def selected (height bound word : Nat) (a : Candidate) : Bool :=
  word.testBit ((keys height bound).idxOf a)

theorem selected_erase {height bound : Nat} (word : Nat)
    (a : PolyominoStripWindow.Candidate Bool height bound) :
    selected height bound word (erase a) = decodeWord height bound word a.1 a.2 := by
  unfold selected decodeWord
  rw [← map_erase_keys,idxOf_map_injective (@erase height bound) erase_injective a]

theorem keys_length (height bound : Nat) :
    (keys height bound).length = stateBits Bool height bound := by
  rw [← map_erase_keys,List.length_map,PolyominoStripWindow.keys_length]

end LeanTrominoes.PolyominoStripWindow.Raw
