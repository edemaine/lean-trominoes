/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyCornerGeometry

/-! # Candidate tests for corner-key matching -/

namespace LeanTrominoes.KeyCornerArithmetic

private def verticalList : List Cell := [(1, 0), (0, 1), (-1, -1), (-1, 1), (4, -2), (-1, 0)]
private def rightList : List Cell := [(1, 0), (-9, 1), (-1, -1), (0, 13), (0, -2), (-1, 1), (1, -1)]

/-- Occupied witnesses relative to the bottom of the vertical lock. -/
def verticalOffsets : Finset Cell := verticalList.toFinset
/-- Occupied witnesses relative to the hooked end of the right lock. -/
def rightOffsets : Finset Cell := rightList.toFinset

/-- The candidate covers the lock cell and avoids the specified occupied cells. -/
def compatible (n : Int) (s : SquareSymmetry) (c : Cell) (offsets : Finset Cell) : Prop :=
  upper n c ∧ ∀ d ∈ offsets, ¬ lower n (Cell.add c (s.inverse.act d))

instance (n : Int) (s : SquareSymmetry) (c : Cell) (offsets : Finset Cell) :
    Decidable (compatible n s c offsets) := by unfold compatible; infer_instance

end LeanTrominoes.KeyCornerArithmetic
