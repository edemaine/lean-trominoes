/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseSolver
import Mathlib.Data.Fin.SuccPred

/-! # Adding an isolated forced pair to a finite bipartite graph

Inactive records in a fixed-size edge table may point to this dummy pair.
Repeated dummy edges have no effect on whether a perfect matching exists.
-/
namespace LeanTrominoes.BipartiteMatching.DummyVertex
variable {n : ℕ}

def extendEquiv (f : Fin n ≃ Fin n) : Fin (n+1) ≃ Fin (n+1) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (f i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (f.symm i).castSucc)
  left_inv x := by refine Fin.lastCases ?_ (fun i => ?_) x <;> simp
  right_inv x := by refine Fin.lastCases ?_ (fun i => ?_) x <;> simp

@[simp] theorem extendEquiv_castSucc (f : Fin n ≃ Fin n) (i : Fin n) :
    extendEquiv f i.castSucc=(f i).castSucc := by simp [extendEquiv]

@[simp] theorem extendEquiv_last (f : Fin n ≃ Fin n) :
    extendEquiv f (Fin.last n)=Fin.last n := by simp [extendEquiv]

private theorem below_last (f : Fin (n+1) ≃ Fin (n+1)) (fixed : f (Fin.last n)=Fin.last n) (i : Fin n) :
    (f i.castSucc).val<n := by
  have bound := (f i.castSucc).isLt
  have different : f i.castSucc≠Fin.last n := by
    intro same
    exact Fin.castSucc_ne_last i (f.injective (same.trans fixed.symm))
  have valNe : (f i.castSucc).val≠n := by
    intro equal
    exact different (Fin.ext equal)
  omega

def shrink (f : Fin (n+1) ≃ Fin (n+1)) (fixed : f (Fin.last n)=Fin.last n) (i : Fin n) : Fin n :=
  ⟨(f i.castSucc).val,below_last f fixed i⟩

@[simp] theorem shrink_castSucc (f : Fin (n+1) ≃ Fin (n+1)) (fixed : f (Fin.last n)=Fin.last n) (i : Fin n) :
    (shrink f fixed i).castSucc=f i.castSucc := Fin.ext rfl

theorem symm_last (f : Fin (n+1) ≃ Fin (n+1)) (fixed : f (Fin.last n)=Fin.last n) :
    f.symm (Fin.last n)=Fin.last n := by
  apply f.injective
  simp [fixed]

def restrictEquiv (f : Fin (n+1) ≃ Fin (n+1)) (fixed : f (Fin.last n)=Fin.last n) : Fin n ≃ Fin n where
  toFun := shrink f fixed
  invFun := shrink f.symm (symm_last f fixed)
  left_inv i := by
    apply Fin.castSucc_injective n
    rw [shrink_castSucc,shrink_castSucc,Equiv.symm_apply_apply]
  right_inv i := by
    apply Fin.castSucc_injective n
    rw [shrink_castSucc,shrink_castSucc,Equiv.apply_symm_apply]

@[simp] theorem restrictEquiv_castSucc (f : Fin (n+1) ≃ Fin (n+1))
    (fixed : f (Fin.last n)=Fin.last n) (i : Fin n) :
    (restrictEquiv f fixed i).castSucc=f i.castSucc := shrink_castSucc f fixed i

def addDummy (edges : List (Fin n × Fin n)) : List (Fin (n+1) × Fin (n+1)) :=
  (Fin.last n,Fin.last n)::edges.map (fun edge => (edge.1.castSucc,edge.2.castSucc))

theorem addDummy_mem (edges : List (Fin n × Fin n)) (l r : Fin (n+1)) :
    (l,r)∈addDummy edges ↔ (l=Fin.last n ∧ r=Fin.last n) ∨
      ∃ a b : Fin n, (a,b)∈edges ∧ l=a.castSucc ∧ r=b.castSucc := by
  simp only [addDummy,List.mem_cons,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro (equal | ⟨⟨a,b⟩,member,equal⟩)
    · exact Or.inl equal
    · exact Or.inr ⟨a,b,member,equal.1.symm,equal.2.symm⟩
  · rintro (equal | ⟨a,b,member,left,right⟩)
    · exact Or.inl equal
    · exact Or.inr ⟨(a,b),member,left.symm,right.symm⟩

/-- Adjacency alone determines the existence of a perfect matching. -/
theorem matching_congr {m : ℕ} (first second : List (Fin m × Fin m))
    (same : ∀ l r, (l,r)∈first ↔ (l,r)∈second) :
    HasFiniteMatching (DenseSearch.edgeBuckets first) ↔ HasFiniteMatching (DenseSearch.edgeBuckets second) := by
  simp only [HasFiniteMatching,DenseSearch.mem_edgeBuckets]
  constructor <;> rintro ⟨f,h⟩
  · exact ⟨f,fun i => (same i (f i)).mp (h i)⟩
  · exact ⟨f,fun i => (same i (f i)).mpr (h i)⟩

/-- Adding one forced isolated pair preserves finite perfect matchability. -/
theorem matching_addDummy (edges : List (Fin n × Fin n)) :
    HasFiniteMatching (DenseSearch.edgeBuckets (addDummy edges)) ↔
      HasFiniteMatching (DenseSearch.edgeBuckets edges) := by
  simp only [HasFiniteMatching,DenseSearch.mem_edgeBuckets]
  constructor
  · rintro ⟨f,supported⟩
    have fixed : f (Fin.last n)=Fin.last n := by
      rcases (addDummy_mem edges _ _).mp (supported (Fin.last n)) with ⟨_,right⟩ | ⟨a,b,_,left,_⟩
      · exact right
      · exact False.elim (Fin.castSucc_ne_last a left.symm)
    refine ⟨restrictEquiv f fixed,?_⟩
    intro i
    rcases (addDummy_mem edges _ _).mp (supported i.castSucc) with ⟨left,_⟩ | ⟨a,b,member,left,right⟩
    · exact False.elim (Fin.castSucc_ne_last i left)
    · have source : i=a := Fin.castSucc_injective n left
      have target : restrictEquiv f fixed i=b := by
        apply Fin.castSucc_injective n
        exact (restrictEquiv_castSucc f fixed i).trans right
      rw [target,source]
      exact member
  · rintro ⟨f,supported⟩
    refine ⟨extendEquiv f,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (addDummy_mem edges _ _).mpr (Or.inl ⟨rfl,extendEquiv_last f⟩)
    · apply (addDummy_mem edges _ _).mpr
      exact Or.inr ⟨j,f j,supported j,rfl,extendEquiv_castSucc f j⟩

end LeanTrominoes.BipartiteMatching.DummyVertex
