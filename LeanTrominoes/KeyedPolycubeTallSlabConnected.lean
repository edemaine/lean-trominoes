/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabGeometry
import LeanTrominoes.KeyedPolycubeKeyAttachment

/-! # Connectivity with any positive cap thickness -/

namespace LeanTrominoes.KeyedPeriodicComplement
namespace TallSlabConstruction

private def previous (height n : Nat) (c : Voxel) : Voxel :=
  if 0 ≤ c.2 ∧ c.2 < slabBodyHeight height then
    if c.1 ∈ square n then (c.1,c.2+1) else (keyStep c.1,c.2)
  else if (slabBodyHeight height : Int) < c.2 then (c.1,c.2-1)
  else if c.1.1 > 0 then ((c.1.1-1,c.1.2),c.2)
  else ((c.1.1,c.1.2-1),c.2)

private def rank (height n : Nat) (c : Voxel) : Nat :=
  if 0 ≤ c.2 ∧ c.2 < slabBodyHeight height then
    2*n + ((slabBodyHeight height : Int)-c.2).toNat + 4*keyRank n c.1
  else (c.1.1+c.1.2).toNat + (c.2-(slabBodyHeight height : Int)).toNat

end TallSlabConstruction

open TallSlabConstruction in
theorem tallSlabTile_connected {height n : Nat} (hh : 3 ≤ height) (hn : 96 ≤ n)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) :
    Polycube.IsConnected (tallSlabTile height n holes) := by
  have body := slabBodyHeight_bounds hh
  apply Polycube.connected_of_predecessor (tallSlabTile height n holes) ((0,0),(slabBodyHeight height : Int))
    (by rw [mem_tallSlabTile]; right; exact ⟨by simp [mem_square]; omega,by omega⟩)
    (previous height n) (rank height n)
  rintro ⟨⟨x,y⟩,z⟩ hc hne
  rcases (mem_tallSlabTile height n holes _).mp hc with ⟨hq,hz⟩ | ⟨hs,hz⟩
  · dsimp only at hq hz
    by_cases hs : (x,y) ∈ square n
    · have bounds := (mem_square n (x,y)).mp hs
      have next : ((x,y),z+1) ∈ tallSlabTile height n holes := by
        rw [mem_tallSlabTile]
        by_cases last : z+1 = slabBodyHeight height
        · exact Or.inr ⟨hs,by omega⟩
        · exact Or.inl ⟨hq,by omega⟩
      simp only [previous,hz,and_self,↓reduceIte,hs]
      refine ⟨next,Or.inr ⟨rfl,Or.inl rfl⟩,?_⟩
      simp only [rank,keyRank,hs,↓reduceIte]
      dsimp at bounds
      split_ifs <;> omega
    · obtain ⟨hl,ha,hr⟩ := keyStep_properties hn (tile_upper hn holes hq) hs
      have hp := lower_tile hn holes admissible hl
      simp only [previous,hz,and_self,↓reduceIte,hs]
      refine ⟨(mem_tallSlabTile height n holes _).mpr (Or.inl ⟨hp,hz⟩),Or.inl ⟨rfl,ha⟩,?_⟩
      simp only [rank]
      split_ifs <;> omega
  · dsimp only at hs hz
    have bounds := (mem_square n (x,y)).mp hs
    dsimp at bounds
    have outside : ¬ (0 ≤ z ∧ z < slabBodyHeight height) := by omega
    simp only [previous,outside,↓reduceIte]
    by_cases above : (slabBodyHeight height : Int) < z
    · simp only [above,↓reduceIte]
      refine ⟨(mem_tallSlabTile height n holes _).mpr (Or.inr ⟨hs,by omega⟩),?_,?_⟩
      · simp [Voxel.FaceAdjacent]
      · simp only [rank,outside,↓reduceIte]
        split_ifs <;> omega
    · have level : z = slabBodyHeight height := by omega
      by_cases hx : x > 0
      · have prev : (x-1,y) ∈ square n := (mem_square n _).mpr (by omega)
        simp only [above,hx,↓reduceIte]
        refine ⟨(mem_tallSlabTile height n holes _).mpr (Or.inr ⟨prev,hz⟩),?_,?_⟩
        · simp [Voxel.FaceAdjacent,Cell.SideAdjacent]
        · simp only [rank,outside,↓reduceIte]
          omega
      · have hy : y > 0 := by
          by_contra neg
          have zero : x = 0 ∧ y = 0 := by omega
          exact hne (by simp [zero.1,zero.2,level])
        have prev : (x,y-1) ∈ square n := (mem_square n _).mpr (by omega)
        simp only [above,hx,↓reduceIte]
        refine ⟨(mem_tallSlabTile height n holes _).mpr (Or.inr ⟨prev,hz⟩),?_,?_⟩
        · simp [Voxel.FaceAdjacent,Cell.SideAdjacent]
        · simp only [rank,outside,↓reduceIte]
          omega

end LeanTrominoes.KeyedPeriodicComplement
