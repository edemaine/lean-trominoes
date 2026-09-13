/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGeometry
import Mathlib.Tactic.IntervalCases

/-! # An upright cap meets one of the reference tile's solid caps -/

namespace LeanTrominoes.SpaceLock

def capOffsets : Finset Voxel :=
  {((0,0),-2), ((0,0),2), ((1,0),-2), ((1,0),2), ((2,0),-2), ((2,0),2),
    ((3,0),-2), ((3,0),2), ((0,1),-2), ((0,1),2), ((0,2),-2), ((0,2),2),
    ((0,3),-2), ((0,3),2)}

def inCap (n : Int) (c : Voxel) : Prop :=
  KeyCornerArithmetic.inBox n c.1 ∧ (c.2 = -1 ∨ c.2 = 3)

private def capStep (s : CubeSymmetry) (z : Int) : Int :=
  if z = -1 ∨ z = 3 then 0 else if s.flip then z + 1 else 3 - z

private def capProbe (s : CubeSymmetry) (z direction : Int) : Voxel :=
  ((if s.axis = 1 then capStep s z else 0,
    if s.axis = 2 then capStep s z else 0), direction)

private theorem probe_mem (s : CubeSymmetry) (upright : s.axis ≠ 0) (z : Int)
    (lo : -1 ≤ z) (hi : z ≤ 3) (direction : Int) (hd : direction = -2 ∨ direction = 2) :
    capProbe s z direction ∈ capOffsets := by
  rcases s with ⟨p,f,axis⟩
  fin_cases axis
  · exact False.elim (upright rfl)
  all_goals
    cases f <;> interval_cases z <;> rcases hd with rfl | rfl <;>
      simp [capProbe, capStep, capOffsets]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
private theorem probe_covers (n : Int) (hn : 5 ≤ n) (s : CubeSymmetry)
    (upright : s.axis ≠ 0) (c : Voxel) (inside : KeyCornerArithmetic.inBox n c.1)
    (height : -1 ≤ c.2 ∧ c.2 ≤ 3) :
    inCap n (Voxel.add c (s.inverseAct (capProbe s c.2 (-2)))) ∨
      inCap n (Voxel.add c (s.inverseAct (capProbe s c.2 2))) := by
  rcases c with ⟨⟨x,y⟩,z⟩
  obtain ⟨hzlo,hzhi⟩ := height
  dsimp at hzlo hzhi
  rcases s with ⟨p,f,axis⟩
  fin_cases axis
  · exact False.elim (upright rfl)
  all_goals
    cases p <;> cases f <;> interval_cases z <;>
      simp [capProbe, capStep, inCap, CubeSymmetry.inverseAct, CubeSymmetry.cycle,
        SquareSymmetry.inverse, SquareSymmetry.act, Voxel.add, Cell.add,
        KeyCornerArithmetic.inBox] at * <;> omega

theorem upright_cap_overlap (n : Int) (hn : 5 ≤ n) (s : CubeSymmetry)
    (upright : s.axis ≠ 0) (c : Voxel) (inside : KeyCornerArithmetic.inBox n c.1)
    (height : -1 ≤ c.2 ∧ c.2 ≤ 3) :
    ∃ d ∈ capOffsets, inCap n (Voxel.add c (s.inverseAct d)) := by
  rcases probe_covers n hn s upright c inside height with h | h
  · exact ⟨capProbe s c.2 (-2), probe_mem s upright c.2 height.1 height.2 _ (Or.inl rfl), h⟩
  · exact ⟨capProbe s c.2 2, probe_mem s upright c.2 height.1 height.2 _ (Or.inr rfl), h⟩

theorem vertical_cap_witnesses {n : Nat} (hn : 96 ≤ n) {d : Voxel} (hd : d ∈ capOffsets) :
    inCap n (Voxel.add ((2,3),1) d) := by
  simp only [capOffsets, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [inCap, Voxel.add, Cell.add, KeyCornerArithmetic.inBox] <;> omega

theorem right_cap_witnesses {n : Nat} (hn : 96 ≤ n) {d : Voxel} (hd : d ∈ capOffsets) :
    inCap n (Voxel.add (((n : Int)-4,2),1) d) := by
  simp only [capOffsets, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [inCap, Voxel.add, Cell.add, KeyCornerArithmetic.inBox] <;> omega

end LeanTrominoes.SpaceLock
