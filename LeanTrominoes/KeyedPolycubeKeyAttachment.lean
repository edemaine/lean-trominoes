/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity
import LeanTrominoes.KeyedComplementEnvelope

/-! # Paths from protruding planar keys back into the square cap -/

namespace LeanTrominoes.KeyedPeriodicComplement

def keyStep (c : Cell) : Cell :=
  if c.1 < 0 then if c.2 = 2 then (c.1, 3) else (c.1 + 1, c.2)
  else if c.1 = 3 then (2, c.2) else (c.1, c.2 - 1)

def keyRank (n : Nat) (c : Cell) : Nat :=
  if c ∈ square n then 0
  else if c.1 < 0 then (-c.1 + if c.2 = 2 then 1 else 0).toNat
  else (c.2 - n + 1 + if c.1 = 3 then 1 else 0).toNat

theorem keyStep_properties {n : Nat} (hn : 96 ≤ n) {c : Cell}
    (hc : KeyCornerArithmetic.upper n c) (hout : c ∉ square n) :
    KeyCornerArithmetic.lower n (keyStep c) ∧ Cell.SideAdjacent c (keyStep c) ∧
      keyRank n (keyStep c) < keyRank n c := by
  have hk : KeyCornerArithmetic.inKey n c := by
    rcases hc with h | h
    · exact False.elim (hout ((mem_square n c).mpr h.1))
    · exact h
  simp only [KeyCornerArithmetic.inKey] at hk
  simp only [keyStep, keyRank, mem_square, KeyCornerArithmetic.lower,
    KeyCornerArithmetic.inBox, KeyCornerArithmetic.inVerticalLock,
    KeyCornerArithmetic.inHorizontalLock, KeyCornerArithmetic.inKey,
    Cell.SideAdjacent] at *
  split_ifs <;> simp_all <;> omega

end LeanTrominoes.KeyedPeriodicComplement
