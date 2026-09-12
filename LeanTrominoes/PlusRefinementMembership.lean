/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement

/-! # A finite membership test for cross refinement -/

namespace LeanTrominoes.PlusRefinement

def parent (c : Cell) : Cell := ((c.1 + 1) / 3, (c.2 + 1) / 3)

def subcell (c : Cell) : Cell := Cell.sub c (Cell.scale 3 (parent c))

theorem parent_pixel (p u : Cell) (hu : u ∈ cross) : parent (pixel p u) = p := by
  simp only [cross, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  all_goals apply Prod.ext <;> dsimp [parent, pixel, Cell.add, Cell.scale] <;> omega

theorem pixel_parent_subcell (c : Cell) : pixel (parent c) (subcell c) = c := by
  apply Prod.ext <;> dsimp [pixel, subcell, Cell.add, Cell.sub, Cell.scale] <;> omega

theorem subcell_pixel (p u : Cell) (hu : u ∈ cross) : subcell (pixel p u) = u := by
  unfold subcell
  rw [parent_pixel p u hu]
  apply Prod.ext <;> dsimp [pixel, Cell.add, Cell.sub, Cell.scale] <;> omega

theorem mem_region_iff (original : Set Cell) (c : Cell) :
    c ∈ region original ↔ parent c ∈ original ∧ subcell c ∈ cross := by
  constructor
  · rintro ⟨p, hp, u, hu, rfl⟩
    rw [parent_pixel p u hu, subcell_pixel p u hu]
    exact ⟨hp, hu⟩
  · rintro ⟨hp, hu⟩
    exact ⟨parent c, hp, subcell c, hu, pixel_parent_subcell c⟩

end LeanTrominoes.PlusRefinement
