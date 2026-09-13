/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripRawKeys

/-! # A uniform finite-loop checker for variable-tile strip transitions

Only placement records are enumerated. Neither graph states nor functions
on finite types are enumerated, and duplicate input cells remain harmless.
-/

namespace LeanTrominoes.PolyominoStripWindow.Raw

/-- Input footprints remain lists, including possible duplicate cells. -/
def tiles (cells : Bool → List Cell) : Bool → Polyomino := fun k => (cells k).toFinset

def Fits (cells : Bool → List Cell) (height bound : Nat) (slot : Slot) : Prop :=
  ∀ c ∈ cells slot.1,
    0 ≤ (slot.2.2 : Int)-bound+(slot.2.1.act c).2 ∧
      (slot.2.2 : Int)-bound+(slot.2.1.act c).2 < height

def Covers (cells : Bool → List Cell) (height bound word y : Nat) (a : Candidate) : Prop :=
  selected height bound word a = true ∧
    ∃ c ∈ cells a.2.1,
      Cell.add ((a.1 : Int),(a.2.2.2 : Int)-bound) (a.2.2.1.act c) = ((bound : Int),(y : Int))

instance (cells : Bool → List Cell) (height bound : Nat) (slot : Slot) :
    Decidable (Fits cells height bound slot) := by unfold Fits; infer_instance

instance (cells : Bool → List Cell) (height bound word y : Nat) (a : Candidate) :
    Decidable (Covers cells height bound word y a) := by unfold Covers; infer_instance

/-- All quantifiers range over explicitly bounded lists of natural records. -/
def Transition (cells : Bool → List Cell) (height bound first second : Nat) : Prop :=
  (∀ slot ∈ slots height bound,
    selected height bound first (0,slot) = true → Fits cells height bound slot) ∧
  (∀ y ∈ List.range height, ∃ a ∈ keys height bound,
    Covers cells height bound first y a ∧
      ∀ b ∈ keys height bound, Covers cells height bound first y b → b = a) ∧
  (∀ column ∈ List.range (2*bound), ∀ slot ∈ slots height bound,
    selected height bound first (column+1,slot) = selected height bound second (column,slot))

instance (cells : Bool → List Cell) (height bound first second : Nat) :
    Decidable (Transition cells height bound first second) := by unfold Transition; infer_instance

def check (cells : Bool → List Cell) (height bound first second : Nat) : Bool :=
  decide (Transition cells height bound first second)

private theorem forall_slots {height bound : Nat} (p : Slot → Prop) :
    (∀ slot ∈ slots height bound, p slot) ↔
      ∀ slot : PolyominoStripWindow.Slot Bool height bound, p (eraseSlot slot) := by
  constructor
  · intro h slot
    exact h _ (mem_slots _ |>.mpr slot.2.2.isLt)
  · intro h slot hs
    exact h (slot.1,slot.2.1,⟨slot.2.2,(mem_slots _).mp hs⟩)

private theorem forall_keys {height bound : Nat} (p : Candidate → Prop) :
    (∀ a ∈ keys height bound, p a) ↔
      ∀ a : PolyominoStripWindow.Candidate Bool height bound, p (erase a) := by
  rw [← map_erase_keys]
  simp only [List.forall_mem_map]
  exact ⟨fun h a => h a (PolyominoStripWindow.mem_keys a),fun h a _ => h a⟩

private theorem exists_keys {height bound : Nat} (p : Candidate → Prop) :
    (∃ a ∈ keys height bound, p a) ↔
      ∃ a : PolyominoStripWindow.Candidate Bool height bound, p (erase a) := by
  rw [← map_erase_keys]
  constructor
  · rintro ⟨a,ha,h⟩
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨b,h⟩
  · rintro ⟨a,h⟩
    exact ⟨erase a,List.mem_map.mpr ⟨a,PolyominoStripWindow.mem_keys a,rfl⟩,h⟩

theorem fits_erase {height bound : Nat} (cells : Bool → List Cell)
    (slot : PolyominoStripWindow.Slot Bool height bound) :
    Fits cells height bound (eraseSlot slot) ↔ ValidSlot (tiles cells) slot := by
  constructor
  · intro h c hc
    obtain ⟨a,ha,eq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
    rw [← eq]
    exact h a (List.mem_toFinset.mp ha)
  · intro h c hc
    exact h _ ((Placement.mem_cells_iff _ _ _).mpr ⟨c,List.mem_toFinset.mpr hc,rfl⟩)

theorem covers_erase {height bound : Nat} (cells : Bool → List Cell) (word y : Nat)
    (a : PolyominoStripWindow.Candidate Bool height bound) :
    Covers cells height bound word y (erase a) ↔
      decodeWord height bound word a.1 a.2 = true ∧
        ((bound : Int),(y : Int)) ∈ (placement a.1.val a.2).cells (tiles cells) := by
  unfold Covers
  rw [selected_erase]
  simp only [Placement.mem_cells_iff,tiles,List.mem_toFinset,
    erase,eraseSlot,placement]

private theorem first_column_iff (cells : Bool → List Cell) (height bound word : Nat) :
    (∀ slot ∈ slots height bound,
      selected height bound word (0,slot) = true → Fits cells height bound slot) ↔
    ∀ slot : PolyominoStripWindow.Slot Bool height bound,
      decodeWord height bound word 0 slot = true → ValidSlot (tiles cells) slot := by
  rw [forall_slots]
  apply forall_congr'
  intro slot
  have bit := selected_erase word (0,slot)
  simpa only [erase,Fin.val_zero] using
    (imp_congr (congrArg (· = true) bit |>.to_iff) (fits_erase cells slot))

private theorem coverage_iff (cells : Bool → List Cell) (height bound word y : Nat) :
    (∃ a ∈ keys height bound, Covers cells height bound word y a ∧
      ∀ b ∈ keys height bound, Covers cells height bound word y b → b = a) ↔
    ∃! a : PolyominoStripWindow.Candidate Bool height bound,
      decodeWord height bound word a.1 a.2 = true ∧
        ((bound : Int),(y : Int)) ∈ (placement a.1.val a.2).cells (tiles cells) := by
  rw [exists_keys]
  simp only [forall_keys,covers_erase,erase_injective.eq_iff,ExistsUnique]

private theorem overlap_iff (height bound first second : Nat) :
    (∀ column ∈ List.range (2*bound), ∀ slot ∈ slots height bound,
      selected height bound first (column+1,slot) = selected height bound second (column,slot)) ↔
    ∀ column : Fin (2*bound),
      decodeWord height bound first column.succ = decodeWord height bound second column.castSucc := by
  simp only [List.mem_range,forall_slots]
  constructor
  · intro h column
    funext slot
    have h' := h column.val column.isLt slot
    have l := selected_erase first (column.succ,slot)
    have r := selected_erase second (column.castSucc,slot)
    exact l.symm.trans (h'.trans r)
  · intro h column hc slot
    have h' := congrFun (h ⟨column,hc⟩) slot
    have l := selected_erase first ((⟨column,hc⟩ : Fin (2*bound)).succ,slot)
    have r := selected_erase second ((⟨column,hc⟩ : Fin (2*bound)).castSucc,slot)
    exact l.trans (h'.trans r.symm)

/-- The uniform checker agrees with the exact finite-state tiling relation. -/
theorem check_correct (cells : Bool → List Cell) (height bound first second : Nat) :
    check cells height bound first second = true ↔ packedTransition (tiles cells) height bound first second := by
  unfold check
  rw [decide_eq_true_eq]
  unfold Transition
  rw [first_column_iff,overlap_iff]
  simp only [coverage_iff,
    packedTransition,LocalWindow.Transition,ValidWindow,List.mem_range]
  have rows : (∀ y, y < height → ∃! a : PolyominoStripWindow.Candidate Bool height bound,
      decodeWord height bound first a.1 a.2 = true ∧
        ((bound : Int),(y : Int)) ∈ (placement a.1.val a.2).cells (tiles cells)) ↔
      (∀ y : Fin height, ∃! a : PolyominoStripWindow.Candidate Bool height bound,
      decodeWord height bound first a.1 a.2 = true ∧
        ((bound : Int),(y.val : Int)) ∈ (placement a.1.val a.2).cells (tiles cells)) := by
    exact ⟨fun h y => h y.val y.isLt,fun h y hy => h ⟨y,hy⟩⟩
  rw [rows]
  exact and_assoc.symm

end LeanTrominoes.PolyominoStripWindow.Raw
