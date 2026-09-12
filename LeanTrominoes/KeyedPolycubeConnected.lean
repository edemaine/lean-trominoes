/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity
import LeanTrominoes.KeyedComplementEnvelope

/-! # The actual keyed background becomes connected under a square cap

Keys extend outside the cap, so containment in the cap is insufficient.
The spanning tree first walks each protruding key back into the square.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

def slabTile (n : Nat) (holes : Polyomino) : Polycube :=
  Polycube.capped (tile n holes) (square n) {0} 1

private def keyStep (c : Cell) : Cell :=
  if c.1 < 0 then if c.2 = 2 then (c.1, 3) else (c.1 + 1, c.2)
  else if c.1 = 3 then (2, c.2) else (c.1, c.2 - 1)

private def keyRank (n : Nat) (c : Cell) : Nat :=
  if c ∈ square n then 0
  else if c.1 < 0 then (-c.1 + if c.2 = 2 then 1 else 0).toNat
  else (c.2 - n + 1 + if c.1 = 3 then 1 else 0).toNat

private theorem keyStep_properties {n : Nat} (hn : 96 ≤ n) {c : Cell}
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

private def predecessor (n : Nat) (c : Voxel) : Voxel :=
  if c.2 = 0 then
    if c.1 ∈ square n then (c.1, 1) else (keyStep c.1, 0)
  else if c.1.1 > 0 then ((c.1.1 - 1, c.1.2), 1)
  else ((c.1.1, c.1.2 - 1), 1)

private def rank (n : Nat) (c : Voxel) : Nat :=
  if c.2 = 0 then 2 * n + keyRank n c.1 else (c.1.1 + c.1.2).toNat

/-- The cap connects all components of Q, including both protruding keys. -/
theorem slabTile_connected {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) : Polycube.IsConnected (slabTile n holes) := by
  apply Polycube.connected_of_predecessor (slabTile n holes) ((0, 0), 1)
    (by simp [slabTile, mem_square]; omega) (predecessor n) (rank n)
  rintro ⟨⟨x, y⟩, z⟩ hc hne
  change ((x, y), z) ∈ Polycube.capped (tile n holes) (square n) {0} 1 at hc
  rw [Polycube.mem_capped] at hc
  rcases hc with ⟨hq, hz⟩ | ⟨hq, hz⟩
  · have hz : z = 0 := Finset.mem_singleton.mp hz
    subst z
    by_cases hs : (x, y) ∈ square n
    · obtain ⟨hx, hx', hy, hy'⟩ := (mem_square _ _).mp hs
      simp [predecessor, hs, slabTile, Voxel.FaceAdjacent, rank, keyRank]
      omega
    · obtain ⟨hl, ha, hr⟩ := keyStep_properties hn (tile_upper hn holes hq) hs
      have hp := lower_tile hn holes admissible hl
      simp only [predecessor, hs, ↓reduceIte]
      refine ⟨?_, Or.inl ⟨rfl, ha⟩, ?_⟩
      · simp [slabTile, hp]
      · simpa [rank] using hr
  · change z = 1 at hz
    subst z
    obtain ⟨hx, hx', hy, hy'⟩ := (mem_square _ _).mp hq
    dsimp at hx hx' hy hy'
    have hne' : x ≠ 0 ∨ y ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hne (by simp [h.1, h.2])
    by_cases hp : x > 0
    · have hs : (x - 1, y) ∈ square n := (mem_square _ _).mpr (by omega)
      simp [predecessor, hp, slabTile, hs, Voxel.FaceAdjacent, Cell.SideAdjacent, rank]
      omega
    · have hs : (x, y - 1) ∈ square n := (mem_square _ _).mpr (by omega)
      simp [predecessor, hp, slabTile, hs, Voxel.FaceAdjacent, Cell.SideAdjacent, rank]
      omega

end LeanTrominoes.KeyedPeriodicComplement
