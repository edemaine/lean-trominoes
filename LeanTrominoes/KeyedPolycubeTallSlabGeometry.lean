/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubesSlabs
import LeanTrominoes.KeyedPolycubeSpaceGeometry
import Mathlib.Data.Int.Interval

/-! # Two or three simulation layers beneath a variable-thickness solid cap -/

namespace LeanTrominoes.KeyedPeriodicComplement

/-- Height three needs two simulation layers; larger slabs use three. -/
def slabBodyHeight (height : Nat) : Nat := if height = 3 then 2 else 3

def tallSlabTile (height n : Nat) (holes : Polyomino) : Polycube :=
  Polycube.extrude (tile n holes) (Finset.Ico (0 : Int) (slabBodyHeight height)) ∪
    Polycube.extrude (square n) (Finset.Ico (slabBodyHeight height : Int) height)

def tallSlabFamily (height n : Nat) (holes : Polyomino) : Bool → Polycube :=
  Polycube.pairTiles (TwoConnectedPolycubes.slabSmall height) (tallSlabTile height n holes)

theorem slabBodyHeight_bounds {height : Nat} (hh : 3 ≤ height) :
    2 ≤ slabBodyHeight height ∧ slabBodyHeight height ≤ 3 ∧ slabBodyHeight height < height := by
  by_cases h : height = 3 <;> simp [slabBodyHeight,h] <;> omega

theorem mem_tallSlabTile (height n : Nat) (holes : Polyomino) (c : Voxel) :
    c ∈ tallSlabTile height n holes ↔
      (c.1 ∈ tile n holes ∧ 0 ≤ c.2 ∧ c.2 < slabBodyHeight height) ∨
      (c.1 ∈ square n ∧ (slabBodyHeight height : Int) ≤ c.2 ∧ c.2 < height) := by
  simp [tallSlabTile]

theorem slabSmall_eq_extrude {height : Nat} (hh : 3 ≤ height) :
    TwoConnectedPolycubes.slabSmall height =
      Polycube.extrude PlusRefinement.bumpy (Finset.Ico (0 : Int) (slabBodyHeight height)) := by
  have two : height ≠ 2 := by omega
  have layers2 : Finset.Ico (0 : Int) 2 = {0,1} := by decide +kernel
  have layers3 : Finset.Ico (0 : Int) 3 = {0,1,2} := by decide +kernel
  by_cases three : height = 3 <;>
    simp [TwoConnectedPolycubes.slabSmall,slabBodyHeight,two,three,
      Polycube.bumpyTwo,Polycube.bumpyThree,layers2,layers3]

end LeanTrominoes.KeyedPeriodicComplement
