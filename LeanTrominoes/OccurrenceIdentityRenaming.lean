/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFInjectiveRenaming

/-! # Extending compiled occurrence identities to an injective atom renaming

The compiler need only preserve equality on the finite occurrence stream.
Unused atoms receive disjoint codes above every emitted identity.
-/
namespace LeanTrominoes.OccurrenceIdentity
variable {V : Type*} [DecidableEq V] [Encodable V]

structure Coherent (atoms : List V) (codes : List Nat) : Prop where
  length_eq : codes.length=atoms.length
  sameCode : ∀ i (hi : i<atoms.length) j (hj : j<atoms.length),
    codes[i]'(by omega)=codes[j]'(by omega) ↔ atoms[i]=atoms[j]

def rename (atoms : List V) (codes : List Nat) (a : V) : Nat :=
  if a∈atoms then codes.getD (atoms.idxOf a) 0 else codes.sum+1+Encodable.encode a

theorem getD_le_sum (codes : List Nat) (i : Nat) : codes.getD i 0 ≤ codes.sum := by
  induction codes generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using le_trans (ih i) (Nat.le_add_left cs.sum c)

theorem rename_le_sum (atoms : List V) (codes : List Nat) (a : V) (ha : a∈atoms) :
    rename atoms codes a ≤ codes.sum := by
  rw [rename,if_pos ha]
  exact getD_le_sum codes _

theorem rename_getElem (atoms : List V) (codes : List Nat) (coherent : Coherent atoms codes)
    (i : Nat) (hi : i<atoms.length) :
    rename atoms codes atoms[i] = codes[i]'(by have := coherent.1; omega) := by
  have member := List.getElem_mem hi
  have indexBound := List.idxOf_lt_length_iff.mpr member
  rw [rename,if_pos member,List.getD_eq_getElem _ _ (show atoms.idxOf atoms[i]<codes.length by have := coherent.1; omega)]
  apply (coherent.2 _ indexBound i hi).mpr
  exact List.getElem_idxOf indexBound

theorem rename_injective (atoms : List V) (codes : List Nat) (coherent : Coherent atoms codes) :
    Function.Injective (rename atoms codes) := by
  intro a b equal
  by_cases ha : a∈atoms <;> by_cases hb : b∈atoms
  · have ia := List.idxOf_lt_length_iff.mpr ha
    have ib := List.idxOf_lt_length_iff.mpr hb
    have ca := coherent.1
    simp only [rename,if_pos ha,if_pos hb,
      List.getD_eq_getElem _ _ (show atoms.idxOf a<codes.length by omega),
      List.getD_eq_getElem _ _ (show atoms.idxOf b<codes.length by omega)] at equal
    have values := (coherent.2 _ ia _ ib).mp equal
    simpa only [List.getElem_idxOf ia,List.getElem_idxOf ib] using values
  · have bound := rename_le_sum atoms codes a ha
    have other : rename atoms codes b = codes.sum+1+Encodable.encode b := by rw [rename,if_neg hb]
    omega
  · have bound := rename_le_sum atoms codes b hb
    have other : rename atoms codes a = codes.sum+1+Encodable.encode a := by rw [rename,if_neg ha]
    omega
  · simp only [rename,if_neg ha,if_neg hb,Nat.add_left_cancel_iff] at equal
    exact Encodable.encode_injective equal

theorem map_rename (atoms : List V) (codes : List Nat) (coherent : Coherent atoms codes) :
    atoms.map (rename atoms codes) = codes := by
  apply List.ext_getElem
  · simpa using coherent.1.symm
  · intro i hi hj
    rw [List.getElem_map]
    exact rename_getElem atoms codes coherent i (by simpa using hi)

end LeanTrominoes.OccurrenceIdentity
