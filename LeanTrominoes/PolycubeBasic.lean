/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

/-! # Integer voxels and all 48 cube symmetries

Choose the extrusion axis, a square symmetry in its perpendicular plane, and
whether to reverse the extrusion. This includes rotations and reflections.
-/

namespace LeanTrominoes

abbrev Voxel := Cell × Int
abbrev Polycube := Finset Voxel

namespace Voxel

def add (a b : Voxel) : Voxel := (Cell.add a.1 b.1, a.2 + b.2)
def sub (a b : Voxel) : Voxel := (Cell.sub a.1 b.1, a.2 - b.2)

@[simp] theorem sub_add (a b : Voxel) : add (sub a b) b = a := by
  rcases a with ⟨⟨x, y⟩, z⟩
  rcases b with ⟨⟨u, v⟩, w⟩
  simp [add, sub, Cell.add, Cell.sub]

theorem add_left_injective (a : Voxel) : Function.Injective (add a) := by
  rintro ⟨⟨x, y⟩, z⟩ ⟨⟨u, v⟩, w⟩ h
  simpa [add, Cell.add] using h

end Voxel

/-- Axis `0` preserves the horizontal plane; axes `1` and `2` turn it upright. -/
structure CubeSymmetry where
  planar : SquareSymmetry
  flip : Bool
  axis : Fin 3
  deriving DecidableEq, Fintype, Repr

namespace CubeSymmetry

/-- The three cyclic coordinate permutations. -/
def cycle : Fin 3 → Voxel ≃ Voxel
  | 0 => Equiv.refl _
  | 1 =>
    { toFun := fun c => ((c.2, c.1.1), c.1.2)
      invFun := fun c => ((c.1.2, c.2), c.1.1)
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl }
  | 2 =>
    { toFun := fun c => ((c.1.2, c.2), c.1.1)
      invFun := fun c => ((c.2, c.1.1), c.1.2)
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl }

def act (s : CubeSymmetry) (c : Voxel) : Voxel :=
  cycle s.axis (s.planar.act c.1, if s.flip then -c.2 else c.2)

def inverseAct (s : CubeSymmetry) (c : Voxel) : Voxel :=
  let d := (cycle s.axis).symm c
  (s.planar.inverse.act d.1, if s.flip then -d.2 else d.2)

@[simp] theorem inverse_act_act (s : CubeSymmetry) (c : Voxel) :
    s.inverseAct (s.act c) = c := by
  simp only [inverseAct, act, Equiv.symm_apply_apply]
  cases s.flip <;> simp

@[simp] theorem act_inverse_act (s : CubeSymmetry) (c : Voxel) :
    s.act (s.inverseAct c) = c := by
  simp only [inverseAct, act, SquareSymmetry.act_inverse_act]
  cases s.flip <;> simp

def voxelEquiv (s : CubeSymmetry) : Voxel ≃ Voxel where
  toFun := s.act
  invFun := s.inverseAct
  left_inv := s.inverse_act_act
  right_inv := s.act_inverse_act

theorem act_injective (s : CubeSymmetry) : Function.Injective s.act :=
  s.voxelEquiv.injective

def identity : CubeSymmetry := ⟨.identity, false, 0⟩

@[simp] theorem identity_act (c : Voxel) : identity.act c = c := rfl

theorem card : Fintype.card CubeSymmetry = 48 := by decide

end CubeSymmetry

structure VoxelPlacement (ι : Type*) where
  kind : ι
  symmetry : CubeSymmetry
  offset : Voxel
  deriving DecidableEq, Repr

namespace VoxelPlacement

@[ext] theorem ext {ι : Type*} {a b : VoxelPlacement ι}
    (hk : a.kind = b.kind) (hs : a.symmetry = b.symmetry)
    (ho : a.offset = b.offset) : a = b := by
  cases a; cases b; simp_all

def cells {ι : Type*} (p : VoxelPlacement ι) (tiles : ι → Polycube) : Polycube :=
  (tiles p.kind).image fun c => Voxel.add p.offset (p.symmetry.act c)

theorem mem_cells_iff {ι : Type*} (p : VoxelPlacement ι) (tiles : ι → Polycube)
    (c : Voxel) : c ∈ p.cells tiles ↔
      ∃ source ∈ tiles p.kind, Voxel.add p.offset (p.symmetry.act source) = c := by
  simp [cells]

end VoxelPlacement
end LeanTrominoes
