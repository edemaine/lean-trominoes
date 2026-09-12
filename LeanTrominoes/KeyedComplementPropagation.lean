/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementRightNeighbor
import LeanTrominoes.TilingTranslation

/-! # Propagation of keyed complements through a quadrant -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- The locks force the two neighbors of every unrotated Q placement. -/
theorem translated_neighbors {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ placements)
    (offset : Cell) (seed : (⟨true, .identity, offset⟩ : Placement Bool) ∈ placements) :
    (⟨true, .identity, Cell.add offset (0, -(n : Int))⟩ : Placement Bool) ∈ placements ∧
      (⟨true, .identity, Cell.add offset ((n : Int), 0)⟩ : Placement Bool) ∈ placements := by
  have reference : referencePlacement ∈ {p : Placement Bool | p.shift offset ∈ placements} := by
    simpa only [Set.mem_setOf_eq, referencePlacement, Placement.shift, Cell.add,
      Int.add_zero, Prod.eta] using seed
  exact ⟨vertical_neighbor hn period holes admissible _ (tiling.recenter offset) reference,
    right_neighbor hn period holes admissible _ (tiling.recenter offset) reference⟩

/-- Every nonnegative combination of the two forced steps occurs. This gives
arbitrarily large canonical grid patches without claiming a global Q grid. -/
theorem quadrant_placements {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ placements)
    (offset : Cell) (seed : (⟨true, .identity, offset⟩ : Placement Bool) ∈ placements)
    (i j : Nat) :
    (⟨true, .identity,
      Cell.add offset ((n : Int) * i, -(n : Int) * j)⟩ : Placement Bool) ∈ placements := by
  induction i with
  | zero =>
    induction j with
    | zero => simpa [Cell.add] using seed
    | succ j ih =>
      have next := (translated_neighbors hn period holes admissible placements tiling _ ih).1
      simpa only [Cell.add, Nat.cast_zero, Int.mul_zero, Int.add_zero, Nat.cast_add,
        Nat.cast_one, Int.mul_add, Int.mul_one, Int.add_assoc] using next
  | succ i ih =>
    have next := (translated_neighbors hn period holes admissible placements tiling _ ih).2
    simpa only [Cell.add, Nat.cast_add, Nat.cast_one, Int.mul_add, Int.mul_one,
      Int.add_zero, Int.add_assoc] using next

end LeanTrominoes.KeyedPeriodicComplement
