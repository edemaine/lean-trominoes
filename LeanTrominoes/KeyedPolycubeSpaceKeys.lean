/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceLockData

/-! # The two finite key prisms embed in every admissible space tile -/

namespace LeanTrominoes.SpaceLock

private theorem height_iff (z : Int) : z ∈ ({0,1,2} : Finset Int) ↔ 0 ≤ z ∧ z ≤ 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem keyPrism_mem (key : Polyomino) (c : Voxel) :
    c ∈ keyPrism key ↔ c.1 ∈ key ∧ 0 ≤ c.2 ∧ c.2 ≤ 2 := by
  rw [keyPrism, Polycube.mem_extrude, height_iff]

theorem vertical_key_embed {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    {q : Voxel} (hq : q ∈ keyPrism KeyedPeriodicComplement.verticalLock) :
    Voxel.add ((0,n),0) q ∈ KeyedPeriodicComplement.spaceTile n holes := by
  obtain ⟨hq,hz⟩ := (keyPrism_mem _ q).mp hq
  apply (KeyedPeriodicComplement.mem_spaceTile n holes _).mpr
  left
  have hv := (KeyedPeriodicComplement.verticalLock_iff q.1).mp hq
  have key : KeyCornerArithmetic.inKey n (Cell.add (0,n) q.1) := by
    simp only [KeyCornerArithmetic.inVerticalLock] at hv
    simp only [KeyCornerArithmetic.inKey, Cell.add]
    omega
  have hp := KeyedPeriodicComplement.lower_tile hn holes admissible (Or.inr key)
  simpa [Voxel.add, Cell.add] using And.intro hp hz

theorem horizontal_key_embed {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    {q : Voxel} (hq : q ∈ keyPrism horizontalKey) :
    Voxel.add ((0,0),0) q ∈ KeyedPeriodicComplement.spaceTile n holes := by
  obtain ⟨hq,hz⟩ := (keyPrism_mem _ q).mp hq
  have key : KeyCornerArithmetic.inKey n q.1 := by
    simp only [horizontalKey, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hq
    simp only [KeyCornerArithmetic.inKey]
    omega
  have hp := KeyedPeriodicComplement.lower_tile hn holes admissible (Or.inr key)
  apply (KeyedPeriodicComplement.mem_spaceTile n holes _).mpr
  left
  simpa [Voxel.add, Cell.add] using And.intro hp hz

theorem key_cases (n : Nat) (q : Voxel) (hk : KeyCornerArithmetic.inKey n q.1)
    (height : 0 ≤ q.2 ∧ q.2 ≤ 2) :
    (∃ r ∈ keyPrism KeyedPeriodicComplement.verticalLock, q = Voxel.add ((0,n),0) r) ∨
      (∃ r ∈ keyPrism horizontalKey, q = Voxel.add ((0,0),0) r) := by
  rcases q with ⟨⟨x,y⟩,z⟩
  dsimp at hk height
  by_cases hv : (x = 2 ∧ (n : Int) ≤ y ∧ y ≤ n + 3) ∨ (x = 3 ∧ y = n + 2)
  · left
    refine ⟨((x,y-n),z), ?_, ?_⟩
    · rw [keyPrism_mem, KeyedPeriodicComplement.verticalLock_iff]
      exact ⟨by simp only [KeyCornerArithmetic.inVerticalLock]; omega, height⟩
    · simp [Voxel.add, Cell.add]
  · right
    refine ⟨((x,y),z), ?_, ?_⟩
    · rw [keyPrism_mem]
      refine ⟨?_,height⟩
      simp only [horizontalKey, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      simp only [KeyCornerArithmetic.inKey] at hk
      omega
    · simp [Voxel.add, Cell.add]

end LeanTrominoes.SpaceLock
