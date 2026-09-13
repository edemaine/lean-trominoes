/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementEnvelope
import LeanTrominoes.PolycubeExtrusion

/-! # A three-layer simulation sandwiched between two solid caps -/

namespace LeanTrominoes.KeyedPeriodicComplement

def spaceTile (n : Nat) (holes : Polyomino) : Polycube :=
  Polycube.extrude (tile n holes) {0, 1, 2} ∪ Polycube.extrude (square n) {-1, 3}

theorem mem_spaceTile (n : Nat) (holes : Polyomino) (c : Voxel) :
    c ∈ spaceTile n holes ↔
      (c.1 ∈ tile n holes ∧ 0 ≤ c.2 ∧ c.2 ≤ 2) ∨
      (c.1 ∈ square n ∧ (c.2 = -1 ∨ c.2 = 3)) := by
  simp only [spaceTile, Finset.mem_union, Polycube.mem_extrude,
    Finset.mem_insert, Finset.mem_singleton]
  have hz : (c.2 = 0 ∨ c.2 = 1 ∨ c.2 = 2) ↔ 0 ≤ c.2 ∧ c.2 ≤ 2 := by omega
  rw [hz]

end LeanTrominoes.KeyedPeriodicComplement

namespace LeanTrominoes.SpaceKeyArithmetic

def upper (n : Int) (c : Voxel) : Prop :=
  (KeyCornerArithmetic.upper n c.1 ∧ 0 ≤ c.2 ∧ c.2 ≤ 2) ∨
    (KeyCornerArithmetic.inBox n c.1 ∧ (c.2 = -1 ∨ c.2 = 3))

def lower (n : Int) (c : Voxel) : Prop :=
  (KeyCornerArithmetic.lower n c.1 ∧ 0 ≤ c.2 ∧ c.2 ≤ 2) ∨
    (KeyCornerArithmetic.inBox n c.1 ∧ (c.2 = -1 ∨ c.2 = 3))

instance (n : Int) (c : Voxel) : Decidable (upper n c) := by
  unfold upper KeyCornerArithmetic.upper KeyCornerArithmetic.inBox
    KeyCornerArithmetic.inVerticalLock KeyCornerArithmetic.inHorizontalLock KeyCornerArithmetic.inKey
  infer_instance

instance (n : Int) (c : Voxel) : Decidable (lower n c) := by
  unfold lower KeyCornerArithmetic.lower KeyCornerArithmetic.inBox
    KeyCornerArithmetic.inVerticalLock KeyCornerArithmetic.inHorizontalLock KeyCornerArithmetic.inKey
  infer_instance

theorem tile_upper {n : Nat} (hn : 96 ≤ n) (holes : Polyomino) {c : Voxel}
    (hc : c ∈ KeyedPeriodicComplement.spaceTile n holes) : upper n c := by
  rcases (KeyedPeriodicComplement.mem_spaceTile n holes c).mp hc with h | h
  · exact Or.inl ⟨KeyedPeriodicComplement.tile_upper hn holes h.1, h.2⟩
  · exact Or.inr ⟨(KeyedPeriodicComplement.mem_square n c.1).mp h.1, h.2⟩

theorem lower_tile {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes) {c : Voxel}
    (hc : lower n c) : c ∈ KeyedPeriodicComplement.spaceTile n holes := by
  apply (KeyedPeriodicComplement.mem_spaceTile n holes c).mpr
  rcases hc with h | h
  · exact Or.inl ⟨KeyedPeriodicComplement.lower_tile hn holes admissible h.1, h.2⟩
  · exact Or.inr ⟨(KeyedPeriodicComplement.mem_square n c.1).mpr h.1, h.2⟩

end LeanTrominoes.SpaceKeyArithmetic
