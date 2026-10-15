/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Int.Basic

/-! # Integer-lattice cell data -/

namespace LeanTrominoes

/-- A unit-square cell, identified by its integer coordinates. -/
abbrev Cell := Int × Int

namespace Cell

/-- Coordinatewise addition of lattice cells/vectors. -/
def add (first second : Cell) : Cell :=
  (first.1 + second.1, first.2 + second.2)

/-- Coordinatewise subtraction of lattice cells/vectors. -/
def sub (first second : Cell) : Cell :=
  (first.1 - second.1, first.2 - second.2)

/-- Integer scaling of a lattice vector. -/
def scale (coefficient : Int) (vector : Cell) : Cell :=
  (coefficient * vector.1, coefficient * vector.2)

/-- Translation by a fixed cell is injective. -/
theorem add_left_injective (offset : Cell) : Function.Injective (add offset) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ equality
  simp only [add, Prod.mk.injEq] at equality ⊢
  exact ⟨Int.add_left_cancel equality.1, Int.add_left_cancel equality.2⟩

/-- Subtracting a fixed cell is injective. -/
theorem sub_right_injective (offset : Cell) :
    Function.Injective (fun cell => sub cell offset) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ equality
  simp only [sub, Prod.mk.injEq] at equality ⊢
  constructor
  · calc
      x₁ = x₁ - offset.1 + offset.1 := (Int.sub_add_cancel _ _).symm
      _ = x₂ - offset.1 + offset.1 :=
        congrArg (fun value => value + offset.1) equality.1
      _ = x₂ := Int.sub_add_cancel _ _
  · calc
      y₁ = y₁ - offset.2 + offset.2 := (Int.sub_add_cancel _ _).symm
      _ = y₂ - offset.2 + offset.2 :=
        congrArg (fun value => value + offset.2) equality.2
      _ = y₂ := Int.sub_add_cancel _ _

end Cell
end LeanTrominoes
