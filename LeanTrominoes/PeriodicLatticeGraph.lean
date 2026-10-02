/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBipartiteCore
import Mathlib.Logic.Relation

/-! # Directed and undirected periodic graphs in arbitrary dimension -/
namespace LeanTrominoes.PeriodicLatticeGraph
abbrev Lattice (d : Nat) := Fin d → Int
structure Arc (V : Type*) (d : Nat) where
  source : V
  target : V
  offset : Lattice d
  deriving DecidableEq, Repr
variable {V : Type*} {d : Nat}
def translate (t : Lattice d) (u : V × Lattice d) : V × Lattice d := (u.1,u.2+t)
def Adj (arcs : List (Arc V d)) (u v : V × Lattice d) : Prop :=
  ∃ e ∈ arcs, e.source=u.1 ∧ e.target=v.1 ∧ v.2=u.2+e.offset
def UndirectedAdj (arcs : List (Arc V d)) (u v : V × Lattice d) : Prop := Adj arcs u v ∨ Adj arcs v u

theorem adj_translate (arcs : List (Arc V d)) (u v : V × Lattice d) (t : Lattice d)
    (edge : Adj arcs u v) : Adj arcs (translate t u) (translate t v) := by
  obtain ⟨e,he,source,target,equal⟩ := edge
  refine ⟨e,he,source,target,?_⟩
  change v.2+t=(u.2+t)+e.offset
  rw [equal]
  abel

theorem undirected_translate (arcs : List (Arc V d)) (u v : V × Lattice d) (t : Lattice d)
    (edge : UndirectedAdj arcs u v) : UndirectedAdj arcs (translate t u) (translate t v) :=
  edge.elim (fun h => Or.inl (adj_translate arcs u v t h)) (fun h => Or.inr (adj_translate arcs v u t h))

def Connected (arcs : List (Arc V d)) : Prop :=
  ∀ u v, Relation.ReflTransGen (UndirectedAdj arcs) u v

def ProperColoring (arcs : List (Arc V d)) (color : V × Lattice d → Bool) : Prop :=
  ∀ u v, UndirectedAdj arcs u v → color u ≠ color v

end LeanTrominoes.PeriodicLatticeGraph
