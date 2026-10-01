/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # Bipartite periodic graphs in arbitrary dimensions

The two finite types are the translation-invariant color classes. Each
protoedge joins `(left,z)` to `(right,z+offset)`. Offsets need not be local.
A perfect matching is an adjacency-preserving bijection between the lifted
color classes, retaining all parallel edges in the finite presentation.
-/
namespace LeanTrominoes.PeriodicBipartite

abbrev Lattice (d : Nat) := Fin d → Int

structure Edge (L R : Type*) (d : Nat) where
  left : L
  right : R
  offset : Lattice d
  deriving DecidableEq, Repr

variable {L R : Type*} {d : Nat}

def Adj (edges : List (Edge L R d)) (u : L × Lattice d) (v : R × Lattice d) : Prop :=
  ∃ e ∈ edges, e.left=u.1 ∧ e.right=v.1 ∧ v.2=u.2+e.offset

def QuotientAdj (edges : List (Edge L R d)) (l : L) (r : R) : Prop :=
  ∃ e ∈ edges, e.left=l ∧ e.right=r

def HasPerfectMatching (edges : List (Edge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d), ∀ u, Adj edges u (f u)

def HasQuotientMatching (edges : List (Edge L R d)) : Prop :=
  ∃ f : L ≃ R, ∀ l, QuotientAdj edges l (f l)

def TranslationInvariant (f : (L × Lattice d) → R × Lattice d) : Prop :=
  ∀ l z t, f (l,z+t)=((f (l,z)).1,(f (l,z)).2+t)

def HasPeriodOneMatching (edges : List (Edge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, Adj edges u (f u)) ∧ TranslationInvariant f

def Edge.reverse (e : Edge L R d) : Edge R L d := ⟨e.right,e.left,-e.offset⟩

theorem adj_reverse (edges : List (Edge L R d)) (u : L × Lattice d) (v : R × Lattice d) :
    Adj (edges.map Edge.reverse) v u ↔ Adj edges u v := by
  constructor
  · rintro ⟨rev,member,hl,hr,hz⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp member
    exact ⟨e,he,hr,hl,by change u.2=v.2+-e.offset at hz; rw [hz]; simp⟩
  · rintro ⟨e,he,hl,hr,hz⟩
    exact ⟨e.reverse,List.mem_map.mpr ⟨e,he,rfl⟩,hr,hl,by rw [hz]; simp [Edge.reverse]⟩

theorem perfect_reverse (edges : List (Edge L R d)) (h : HasPerfectMatching edges) :
    HasPerfectMatching (edges.map Edge.reverse) := by
  obtain ⟨f,hf⟩ := h
  refine ⟨f.symm,fun v => (adj_reverse edges _ _).mpr ?_⟩
  simpa using hf (f.symm v)

/-- A uniform coordinate bound for the finite offset table. -/
def radius : List (Edge L R d) → Nat
  | [] => 0
  | e::es => max (Finset.univ.sup (fun i => (e.offset i).natAbs)) (radius es)

theorem offset_bound (edges : List (Edge L R d)) (e : Edge L R d) (he : e ∈ edges) (i : Fin d) :
    (e.offset i).natAbs ≤ radius edges := by
  induction edges with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with eq | member
    · subst e
      exact (Finset.le_sup (f := fun j => (a.offset j).natAbs) (Finset.mem_univ i)).trans (Nat.le_max_left _ _)
    · exact (ih member).trans (Nat.le_max_right _ _)

end LeanTrominoes.PeriodicBipartite
