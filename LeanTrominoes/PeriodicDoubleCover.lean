/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicLatticeGraph
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Doubling the generators of a finite periodic graph presentation -/
namespace LeanTrominoes.PeriodicLatticeGraph.DoubleCover
variable {V : Type*} {d : Nat}
abbrev Phase (d : Nat) := Fin d → Fin 2

def residue (z : Lattice d) : Phase d := fun i =>
  ⟨(z i % 2).toNat,by
    have := Int.emod_nonneg (z i) (by omega : (2 : Int) ≠ 0)
    have := Int.emod_lt_of_pos (z i) (by omega : (0 : Int)<2)
    omega⟩
def quotient (z : Lattice d) : Lattice d := fun i => z i / 2
def combine (p : Phase d) (z : Lattice d) : Lattice d := fun i => (p i : Nat)+2*z i

@[simp] theorem residue_combine (p : Phase d) (z : Lattice d) : residue (combine p z)=p := by
  funext i
  apply Fin.ext
  have := (p i).isLt
  simp only [residue,combine]
  omega
@[simp] theorem quotient_combine (p : Phase d) (z : Lattice d) : quotient (combine p z)=z := by
  funext i
  have := (p i).isLt
  simp only [quotient,combine]
  omega
@[simp] theorem combine_split (z : Lattice d) : combine (residue z) (quotient z)=z := by
  funext i
  have := Int.emod_nonneg (z i) (by omega : (2 : Int) ≠ 0)
  simp only [combine,residue,quotient]
  omega

def equivalence (V : Type*) (d : Nat) : ((V × Phase d) × Lattice d) ≃ (V × Lattice d) where
  toFun x := (x.1.1,combine x.1.2 x.2)
  invFun x := ((x.1,residue x.2),quotient x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem combine_add (p : Phase d) (z t : Lattice d) : combine p (z+t)=combine p z+(t+t) := by
  funext i
  simp only [combine,Pi.add_apply]
  omega

theorem equivalence_translate (x : (V × Phase d) × Lattice d) (t : Lattice d) :
    equivalence V d (translate t x)=translate (t+t) (equivalence V d x) := by
  exact Prod.ext rfl (combine_add _ _ _)

def expand (e : Arc V d) (p : Phase d) : Arc (V × Phase d) d :=
  ⟨(e.source,p),(e.target,residue (combine p 0+e.offset)),quotient (combine p 0+e.offset)⟩

def phases (d : Nat) : List (Phase d) :=
  (List.finRange (2^d)).map finFunctionFinEquiv.symm

@[simp] theorem mem_phases (p : Phase d) : p∈phases d := by
  exact List.mem_map.mpr ⟨finFunctionFinEquiv p,List.mem_finRange _,Equiv.symm_apply_apply _ _⟩
@[simp] theorem phases_length : (phases d).length=2^d := by simp [phases]

def arcs (edges : List (Arc V d)) : List (Arc (V × Phase d) d) :=
  (phases d).flatMap fun p => edges.map fun e => expand e p

theorem arcs_length (edges : List (Arc V d)) : (arcs edges).length=edges.length*2^d := by
  simp [arcs,List.length_flatMap,List.map_const,Nat.mul_comm]

theorem expand_target (e : Arc V d) (p : Phase d) (z : Lattice d) :
    combine (expand e p).target.2 (z+(expand e p).offset)=combine p z+e.offset := by
  change combine (residue (combine p 0+e.offset)) (z+quotient (combine p 0+e.offset))=_
  rw [add_comm z,combine_add,combine_split]
  funext i
  simp only [combine,Pi.add_apply,Pi.zero_apply]
  omega

theorem adj_iff (edges : List (Arc V d)) (x y : (V × Phase d) × Lattice d) :
    Adj (arcs edges) x y ↔ Adj edges (equivalence V d x) (equivalence V d y) := by
  constructor
  · rintro ⟨a,ha,source,target,offset⟩
    obtain ⟨p,_,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    refine ⟨e,he,congrArg Prod.fst source,congrArg Prod.fst target,?_⟩
    change combine y.1.2 y.2=combine x.1.2 x.2+e.offset
    rw [offset,← congrArg Prod.snd source,← congrArg Prod.snd target]
    exact expand_target e p x.2
  · rintro ⟨e,he,source,target,offset⟩
    refine ⟨expand e x.1.2,List.mem_flatMap.mpr ⟨x.1.2,mem_phases _,List.mem_map.mpr ⟨e,he,rfl⟩⟩,?_,?_,?_⟩
    · exact Prod.ext source rfl
    · apply Prod.ext target
      have h := expand_target e x.1.2 x.2
      change combine y.1.2 y.2=combine x.1.2 x.2+e.offset at offset
      have eq := congrArg residue (h.trans offset.symm)
      simpa only [residue_combine] using eq
    · have h := expand_target e x.1.2 x.2
      change combine y.1.2 y.2=combine x.1.2 x.2+e.offset at offset
      have eq := congrArg quotient (h.trans offset.symm)
      simpa only [quotient_combine] using eq.symm

theorem undirected_iff (edges : List (Arc V d)) (x y : (V × Phase d) × Lattice d) :
    UndirectedAdj (arcs edges) x y ↔ UndirectedAdj edges (equivalence V d x) (equivalence V d y) := by
  simp only [UndirectedAdj,adj_iff]

end LeanTrominoes.PeriodicLatticeGraph.DoubleCover
