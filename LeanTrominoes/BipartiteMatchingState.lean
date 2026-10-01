/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Indexed partial bipartite matchings and their primitive updates

The functions denote indexed arrays. Consistency is the mutual-inverse
invariant, so every matched vertex has exactly one partner.
-/
namespace LeanTrominoes.BipartiteMatching
variable {L R : Type*}

structure State (L R : Type*) where
  left : L → Option R
  right : R → Option L

def Consistent (s : State L R) : Prop := ∀ l r, s.left l=some r ↔ s.right r=some l

def Supported (adj : L → R → Prop) (s : State L R) : Prop :=
  ∀ l r, s.left l=some r → adj l r

def empty : State L R := ⟨fun _ => none,fun _ => none⟩
theorem empty_consistent : Consistent (empty : State L R) := by simp [Consistent,empty]
theorem empty_supported (adj : L → R → Prop) : Supported adj (empty : State L R) := by
  simp [Supported,empty]

variable [DecidableEq L] [DecidableEq R]

def pair (s : State L R) (l : L) (r : R) : State L R :=
  ⟨Function.update s.left l (some r),Function.update s.right r (some l)⟩

def unpair (s : State L R) (l : L) (r : R) : State L R :=
  ⟨Function.update s.left l none,Function.update s.right r none⟩

theorem pair_consistent (s : State L R) (consistent : Consistent s) (l : L) (r : R)
    (freeL : s.left l=none) (freeR : s.right r=none) : Consistent (pair s l r) := by
  intro a b
  by_cases hl : a=l <;> by_cases hr : b=r
  · subst a; subst b; simp [pair]
  · subst a
    have old : s.right b ≠ some l := by
      intro h
      have := (consistent l b).mpr h
      simp_all
    simp [pair,hr,Ne.symm hr,old]
  · subst b
    have old : s.left a ≠ some r := by
      intro h
      have := (consistent a r).mp h
      simp_all
    simp [pair,hl,Ne.symm hl,old]
  · simpa [pair,hl,hr] using consistent a b

theorem pair_supported (adj : L → R → Prop) (s : State L R) (supported : Supported adj s)
    (l : L) (r : R) (edge : adj l r) : Supported adj (pair s l r) := by
  intro a b h
  by_cases eq : a=l
  · subst a
    have rb : r=b := by simpa [pair] using h
    subst b
    exact edge
  · exact supported a b (by simpa [pair,eq] using h)

theorem unpair_consistent (s : State L R) (consistent : Consistent s) (l : L) (r : R)
    (paired : s.left l=some r) : Consistent (unpair s l r) := by
  intro a b
  by_cases hl : a=l <;> by_cases hr : b=r
  · subst a; subst b; simp [unpair]
  · subst a
    have old : s.right b ≠ some l := by
      intro h
      have := (consistent l b).mpr h
      simp_all
    simp [unpair,hr,old]
  · subst b
    have old : s.left a ≠ some r := by
      intro h
      have one := (consistent a r).mp h
      have two := (consistent l r).mp paired
      simp_all
    simp [unpair,hl,old]
  · simpa [unpair,hl,hr] using consistent a b

theorem unpair_supported (adj : L → R → Prop) (s : State L R) (supported : Supported adj s)
    (l : L) (r : R) : Supported adj (unpair s l r) := by
  intro a b h
  by_cases eq : a=l
  · simp [unpair,eq] at h
  · exact supported a b (by simpa [unpair,eq] using h)

variable [Fintype L]
def domain (s : State L R) : Finset L := Finset.univ.filter (fun l => (s.left l).isSome)
def size (s : State L R) : Nat := (domain s).card

theorem pair_size (s : State L R) (l : L) (r : R) (free : s.left l=none) :
    size (pair s l r)=size s+1 := by
  have equal : domain (pair s l r)=insert l (domain s) := by
    ext a
    by_cases eq : a=l <;> simp [domain,pair,eq]
  have absent : l ∉ domain s := by simp [domain,free]
  simp [size,equal,absent]

theorem unpair_size (s : State L R) (l : L) (r : R) (paired : s.left l=some r) :
    size (unpair s l r)+1=size s := by
  have equal : domain (unpair s l r)=(domain s).erase l := by
    ext a
    by_cases eq : a=l <;> simp [domain,unpair,eq]
  have member : l ∈ domain s := by simp [domain,paired]
  simp only [size,equal,Finset.card_erase_of_mem member]
  have := Finset.card_pos.mpr ⟨l,member⟩
  omega

end LeanTrominoes.BipartiteMatching
