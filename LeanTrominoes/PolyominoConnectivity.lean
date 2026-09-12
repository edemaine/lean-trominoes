/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lean.Elab.Tactic.Omega

/-! # Connectivity through shared sides of unit cells -/

namespace LeanTrominoes

/-- Side adjacency, excluding diagonal contact. -/
def Cell.SideAdjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
    (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

instance : DecidableRel Cell.SideAdjacent := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The side-adjacency graph on the cells of a finite shape. -/
def Polyomino.sideGraph (shape : Polyomino) : SimpleGraph {c // c ∈ shape} where
  Adj a b := Cell.SideAdjacent a.val b.val
  symm := ⟨by intro a b h; unfold Cell.SideAdjacent at *; omega⟩
  loopless := ⟨by intro a h; unfold Cell.SideAdjacent at h; omega⟩

/-- A connected polyomino is nonempty and connected through shared sides. -/
def Polyomino.IsConnected (shape : Polyomino) : Prop := shape.sideGraph.Connected

end LeanTrominoes
