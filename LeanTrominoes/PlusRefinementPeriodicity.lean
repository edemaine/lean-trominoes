/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SquarePeriodicity
import LeanTrominoes.PlusRefinementGeometry

/-! # Periods and translation of cross-refined regions -/

namespace LeanTrominoes.PlusRefinement

theorem region_translate_iff (original : Set Cell) (offset c : Cell) :
    Cell.add (Cell.scale 3 offset) c ∈ region original ↔
      c ∈ region {p | Cell.add offset p ∈ original} := by
  constructor
  · rintro ⟨p, hp, u, hu, eq⟩
    refine ⟨Cell.sub p offset, ?_, u, hu, ?_⟩
    · have cancel : Cell.add offset (Cell.sub p offset) = p := by
        apply Prod.ext <;> dsimp [Cell.add, Cell.sub] <;> omega
      change _ ∈ original
      rwa [cancel]
    · have ex := congrArg Prod.fst eq
      have ey := congrArg Prod.snd eq
      apply Prod.ext <;> dsimp [pixel, Cell.add, Cell.sub, Cell.scale] at ex ey ⊢ <;> omega
  · rintro ⟨p, hp, u, hu, rfl⟩
    refine ⟨Cell.add offset p, hp, u, hu, ?_⟩
    apply Prod.ext <;> dsimp [pixel, Cell.add, Cell.scale] <;> omega

theorem isSquarePeriodic {n : Nat} {original : Set Cell} (periodic : IsSquarePeriodic n original) :
    IsSquarePeriodic (3 * n) (region original) := by
  intro c i j
  have shifted : {p | Cell.add ((n : Int) * i, (n : Int) * j) p ∈ original} = original := by
    ext p
    exact periodic p i j
  have h := region_translate_iff original ((n : Int) * i, (n : Int) * j) c
  rw [shifted] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Cell.scale, Int.mul_assoc] using h

end LeanTrominoes.PlusRefinement
