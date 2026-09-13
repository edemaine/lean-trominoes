/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceGeometry

/-! # Finite occupied witnesses around the two full-space side locks -/

namespace LeanTrominoes.SpaceLock

def verticalOffsets : Finset Voxel :=
  {((-1,0),0), ((0,1),0), ((1,0),0), ((-1,0),-1), ((-1,0),1),
    ((0,0),-2), ((0,0),2), ((1,0),-1), ((1,0),1),
    ((-1,-1),0), ((-1,1),0), ((4,-2),0)}

def rightOffsets : Finset Voxel :=
  {((-1,0),0), ((0,-1),0), ((1,0),0), ((-1,0),-1), ((-1,0),1),
    ((0,0),-2), ((0,0),2), ((0,2),0),
    ((-9,1),0), ((-1,-1),0), ((0,13),0), ((0,-2),0), ((-1,1),0), ((1,-1),0)}

def horizontalKey : Polyomino := {(-4,2), (-4,3), (-3,3), (-2,3), (-1,3)}

def keyPrism (key : Polyomino) : Polycube := Polycube.extrude key {0,1,2}

def ForcedOverlap (shape : Polycube) (offsets : Finset Voxel) (s : CubeSymmetry) : Prop :=
  ∀ q ∈ shape, ∃ d ∈ offsets, Voxel.add q (s.inverseAct d) ∈ shape

instance (shape : Polycube) (offsets : Finset Voxel) (s : CubeSymmetry) :
    Decidable (ForcedOverlap shape offsets s) := by unfold ForcedOverlap; infer_instance

theorem vertical_witnesses {n : Nat} (hn : 96 ≤ n) {d : Voxel} (hd : d ∈ verticalOffsets) :
    SpaceKeyArithmetic.lower n (Voxel.add ((2,3),1) d) := by
  simp only [verticalOffsets, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SpaceKeyArithmetic.lower, Voxel.add, Cell.add, KeyCornerArithmetic.lower,
      KeyCornerArithmetic.inBox, KeyCornerArithmetic.inVerticalLock,
      KeyCornerArithmetic.inHorizontalLock, KeyCornerArithmetic.inKey] <;> omega

theorem right_witnesses {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    {d : Voxel} (hd : d ∈ rightOffsets) :
    SpaceKeyArithmetic.lower n (Voxel.add (((n : Int)-4,2),1) d) := by
  simp only [rightOffsets, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SpaceKeyArithmetic.lower, Voxel.add, Cell.add, KeyCornerArithmetic.lower,
      KeyCornerArithmetic.inBox, KeyCornerArithmetic.inVerticalLock,
      KeyCornerArithmetic.inHorizontalLock, KeyCornerArithmetic.inKey] <;> omega

end LeanTrominoes.SpaceLock
