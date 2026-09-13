/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripRawKeys

/-! # Direct arithmetic addresses for placement bits -/

namespace LeanTrominoes.PolyominoStripWindow.Raw

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

private theorem idxOf_product {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (xs : List α) (ys : List β) (a : α) (b : β) (ha : a ∈ xs) (hb : b ∈ ys) :
    (xs.product ys).idxOf (a,b) = xs.idxOf a * ys.length + ys.idxOf b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.product,List.flatMap_cons]
    by_cases h : x = a
    · subst x
      rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨b,hb,rfl⟩)]
      have eq := idxOf_map_injective (fun y : β => (a,y)) (fun _ _ h => Prod.mk.inj h |>.2) b ys
      simpa using eq
    · have missing : (a,b) ∉ ys.map (fun y => (x,y)) := by simp [h]
      rw [List.idxOf_append_of_notMem missing,List.length_map]
      have rest := ih ((List.mem_cons.mp ha).resolve_left (Ne.symm h))
      change ys.length + (xs.product ys).idxOf (a,b) = _
      rw [rest,List.idxOf_cons_ne xs h]
      simp only [Nat.succ_mul]
      omega

private theorem idxOf_range_of_lt (n i : Nat) (hi : i < n) :
    (List.range n).idxOf i = i := by
  have hlen : i < (List.range n).length := by simpa using hi
  have eq : (List.range n)[i] = i := List.getElem_range hlen
  exact (congrArg (fun v => (List.range n).idxOf v) eq).symm.trans
    ((List.nodup_range (n := n)).idxOf_getElem i hlen)

def symmetryIndex : SquareSymmetry → Nat
  | .identity => 0
  | .rotate90 => 1
  | .rotate180 => 2
  | .rotate270 => 3
  | .reflectX => 4
  | .reflectDiagonal => 5
  | .reflectY => 6
  | .reflectAntidiagonal => 7

theorem symmetryIndex_eq_idxOf (s : SquareSymmetry) : symmetryIndex s = symmetries.idxOf s := by
  cases s <;> decide

def address (height bound : Nat) (a : Candidate) : Nat :=
  ((a.1 * 2 + a.2.1.toNat) * 8 + symmetryIndex a.2.2.1) * (height+2*bound+1) + a.2.2.2

/-- Computing a placement address requires no search through the key list. -/
theorem idxOf_keys_eq_address (height bound : Nat) (a : Candidate) (ha : a ∈ keys height bound) :
    (keys height bound).idxOf a = address height bound a := by
  obtain ⟨hc,hy⟩ := (mem_keys a).mp ha
  rcases a with ⟨column,kind,symmetry,y⟩
  have slotsEq : slots height bound = [false,true].product (symmetries.product (List.range (height+2*bound+1))) := by
    simp [slots,List.product,List.map_flatMap,List.map_map,Function.comp_def]
  have keysEq : keys height bound = (List.range (2*bound+1)).product (slots height bound) := rfl
  rw [keysEq,idxOf_product _ _ _ _ (List.mem_range.mpr hc) ((mem_slots _).mpr hy),slotsEq]
  rw [idxOf_product _ _ _ _ (by cases kind <;> simp) (by simp [mem_symmetries,hy])]
  rw [idxOf_product _ _ _ _ (mem_symmetries symmetry) (List.mem_range.mpr hy)]
  rw [idxOf_range_of_lt _ _ hc,idxOf_range_of_lt _ _ hy]
  simp only [← symmetryIndex_eq_idxOf]
  cases kind <;> simp [address,symmetries,List.product] <;> ring

theorem selected_eq_testBit_address (height bound word : Nat) (a : Candidate)
    (ha : a ∈ keys height bound) :
    selected height bound word a = word.testBit (address height bound a) := by
  rw [selected,idxOf_keys_eq_address height bound a ha]

end LeanTrominoes.PolyominoStripWindow.Raw
