/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivity

/-! # Certifying disconnected polyominoes by a separated component -/

namespace LeanTrominoes.Polyomino

/-- A nonempty proper group of cells closed under side adjacency witnesses
disconnectedness. -/
theorem not_connected_of_closed (shape : Polyomino) (part : Set Cell)
    (closed : ∀ a ∈ shape, a ∈ part → ∀ b ∈ shape, Cell.SideAdjacent a b → b ∈ part)
    (a b : Cell) (ha : a ∈ shape) (hb : b ∈ shape) (inside : a ∈ part) (outside : b ∉ part) :
    ¬ IsConnected shape := by
  intro connected
  change shape.sideGraph.Connected at connected
  have invariant {u v : {c // c ∈ shape}} (walk : shape.sideGraph.Walk u v) :
      u.val ∈ part → v.val ∈ part := by
    induction walk with
    | nil => exact id
    | @cons u v w edge walk ih =>
      intro hu
      exact ih (closed u.val u.property hu v.val v.property edge)
  obtain ⟨walk⟩ := connected ⟨a, ha⟩ ⟨b, hb⟩
  exact outside (invariant walk inside)

end LeanTrominoes.Polyomino
