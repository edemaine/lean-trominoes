/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Union

/-!
# Refinement by five-cell crosses

The cell at `c` is replaced by the cross centered at `3 • c`. This is the
refinement used for the fixed 15-omino in the two-polyomino construction.
-/

namespace LeanTrominoes.PlusRefinement

/-- The five subcells replacing one cell. -/
def cross : Polyomino := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The refined cell with parent `parent` and local position `subcell`. -/
def pixel (parent subcell : Cell) : Cell := Cell.add (Cell.scale 3 parent) subcell

/-- Refinement of a finite prototile. -/
def polyomino (shape : Polyomino) : Polyomino :=
  shape.biUnion fun parent => cross.image (pixel parent)

/-- Refinement of an arbitrary, possibly infinite region. -/
def region (original : Set Cell) : Set Cell :=
  {c | ∃ parent ∈ original, ∃ subcell ∈ cross, pixel parent subcell = c}

theorem mem_polyomino (shape : Polyomino) (c : Cell) :
    c ∈ polyomino shape ↔ ∃ parent ∈ shape, ∃ subcell ∈ cross, pixel parent subcell = c := by
  simp [polyomino]

/-- Subcells have a unique parent, including at negative coordinates. -/
theorem pixel_injective {a b u v : Cell} (hu : u ∈ cross) (hv : v ∈ cross)
    (h : pixel a u = pixel b v) : a = b ∧ u = v := by
  have bounds (c : Cell) (hc : c ∈ cross) :
      -1 ≤ c.1 ∧ c.1 ≤ 1 ∧ -1 ≤ c.2 ∧ c.2 ≤ 1 := by
    simp only [cross, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨ux₀, ux₁, uy₀, uy₁⟩ := bounds u hu
  obtain ⟨vx₀, vx₁, vy₀, vy₁⟩ := bounds v hv
  simp only [pixel, Cell.add, Cell.scale, Prod.mk.injEq] at h
  constructor <;> apply Prod.ext <;> omega

/-- The fixed tile used with the input-dependent disconnected complement. -/
def bumpy : Polyomino := polyomino Tromino.I.cells

theorem bumpy_card : bumpy.card = 15 := by decide

theorem origin_mem_bumpy : (0, 0) ∈ bumpy := by decide

end LeanTrominoes.PlusRefinement
