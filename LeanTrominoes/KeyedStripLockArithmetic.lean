/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedStripOrientation
import LeanTrominoes.KeyedComplementRightNeighbor

/-! # Horizontal lock matching in the bounded strip -/

namespace LeanTrominoes.KeyedStripComplement

open KeyCornerArithmetic (source rightOffsets inBox inHorizontalLock)

set_option maxHeartbeats 2000000 in
theorem right_match (n : Int) (hn : 96 ≤ n) (period : n % 3 = 0)
    (s : SquareSymmetry) (offset : Cell)
    (orientation : (s = .identity ∧ offset.2 = 0) ∨
      (s = .reflectY ∧ offset.2 = 0) ∨
      (s = .reflectX ∧ offset.2 = n - 1) ∨
      (s = .rotate180 ∧ offset.2 = n - 1))
    (covers : upper n (source s offset (n-4,2)))
    (avoids : ∀ d ∈ rightOffsets, ¬ lower n (source s offset (Cell.add (n-4,2) d))) :
    s = .identity ∧ offset = (n,0) := by
  have a := avoids (1,0) (by decide)
  have b := avoids (-9,1) (by decide)
  have c := avoids (-1,-1) (by decide)
  clear avoids
  cases s <;>
    simp [source, SquareSymmetry.inverse, SquareSymmetry.act, Cell.sub, Cell.add,
      upper, lower, inBox, inHorizontalLock, inKey, Prod.ext_iff] at * <;> omega

end LeanTrominoes.KeyedStripComplement
