/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGeometry
import LeanTrominoes.KeyedPolycubeKeyAttachment

/-! # Connectivity of the solid-cap full-space tile -/

namespace LeanTrominoes.KeyedPeriodicComplement
namespace SpaceConstruction

private def previous (n : Nat) (c : Voxel) : Voxel :=
  if 0 ≤ c.2 ∧ c.2 ≤ 2 then
    if c.1 ∈ square n then (c.1, c.2 + 1) else (keyStep c.1, c.2)
  else if c.1.1 > 0 then ((c.1.1 - 1, c.1.2), c.2)
  else if c.1.2 > 0 then ((c.1.1, c.1.2 - 1), c.2)
  else ((0, 0), 0)

private def rank (n : Nat) (c : Voxel) : Nat :=
  if 0 ≤ c.2 ∧ c.2 ≤ 2 then 2 * n + (3 - c.2).toNat + 4 * keyRank n c.1
  else if c.2 = -1 then 4 * n + 4 + (c.1.1 + c.1.2).toNat
  else (c.1.1 + c.1.2).toNat

end SpaceConstruction

open SpaceConstruction in
theorem spaceTile_connected {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) : Polycube.IsConnected (spaceTile n holes) := by
  have origin : (0, 0) ∈ tile n holes := lower_tile hn holes admissible
    (by simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
      KeyCornerArithmetic.inKey]; omega)
  apply Polycube.connected_of_predecessor (spaceTile n holes) ((0, 0), 3)
    (by rw [mem_spaceTile]; right; simp [mem_square]; omega) (previous n) (rank n)
  rintro ⟨⟨x,y⟩,z⟩ hc hne
  rcases (mem_spaceTile n holes _).mp hc with ⟨hq, hz⟩ | ⟨hs, hz⟩
  · dsimp only at hq hz
    by_cases hs : (x,y) ∈ square n
    · have bounds := (mem_square n (x,y)).mp hs
      have next : ((x,y),z+1) ∈ spaceTile n holes := by
        rw [mem_spaceTile]
        by_cases hz2 : z = 2
        · right; exact ⟨hs, Or.inr (by omega)⟩
        · left; exact ⟨hq, by omega⟩
      simp only [previous, hz, and_self, ↓reduceIte, hs]
      refine ⟨next, Or.inr ⟨rfl, Or.inl rfl⟩, ?_⟩
      simp only [rank, keyRank, hs, ↓reduceIte]
      dsimp at bounds
      split_ifs <;> omega
    · obtain ⟨hl, ha, hr⟩ := keyStep_properties hn (tile_upper hn holes hq) hs
      have hp := lower_tile hn holes admissible hl
      simp only [previous, hz, and_self, ↓reduceIte, hs]
      refine ⟨(mem_spaceTile n holes _).mpr (Or.inl ⟨hp,hz⟩), Or.inl ⟨rfl,ha⟩, ?_⟩
      simp only [rank]
      split_ifs <;> omega
  · dsimp only at hs hz
    have bounds := (mem_square n (x,y)).mp hs
    dsimp at bounds
    have hout : ¬ (0 ≤ z ∧ z ≤ 2) := by omega
    simp only [previous, hout, ↓reduceIte]
    by_cases hx : x > 0
    · have hprev : (x-1,y) ∈ square n := (mem_square n _).mpr (by omega)
      simp only [hx, ↓reduceIte]
      refine ⟨(mem_spaceTile n holes _).mpr (Or.inr ⟨hprev,hz⟩), ?_, ?_⟩
      · simp [Voxel.FaceAdjacent, Cell.SideAdjacent]
      · simp only [rank, hout, ↓reduceIte]
        split_ifs <;> omega
    · by_cases hy : y > 0
      · have hprev : (x,y-1) ∈ square n := (mem_square n _).mpr (by omega)
        simp only [hx, hy, ↓reduceIte]
        refine ⟨(mem_spaceTile n holes _).mpr (Or.inr ⟨hprev,hz⟩), ?_, ?_⟩
        · simp [Voxel.FaceAdjacent, Cell.SideAdjacent]
        · simp only [rank, hout, ↓reduceIte]
          split_ifs <;> omega
      · have xy : x = 0 ∧ y = 0 := by omega
        have zz : z = -1 := by
          rcases hz with h | h
          · exact h
          · exact False.elim (hne (by simp [xy.1,xy.2,h]))
        rcases xy with ⟨rfl,rfl⟩
        subst z
        simp only [hx, hy, ↓reduceIte]
        refine ⟨(mem_spaceTile n holes _).mpr (Or.inl ⟨origin, by omega⟩), ?_, ?_⟩
        · simp [Voxel.FaceAdjacent]
        · simp [rank, keyRank, mem_square, show 0 < n by omega]; omega

end LeanTrominoes.KeyedPeriodicComplement
