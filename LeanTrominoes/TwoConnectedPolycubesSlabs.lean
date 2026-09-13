/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubes
import LeanTrominoes.BumpyPolycubeTwoSlab
import LeanTrominoes.BumpyPolycubeSlab
import LeanTrominoes.BumpyPolycubeObstruction
import LeanTrominoes.PolycubeSlabStack

/-! # Targets and fixed-tile obstructions for every slab height greater than one -/

namespace LeanTrominoes.TwoConnectedPolycubes

/-- The small tile is independent of the input, and has at most 45 voxels. -/
def slabSmall (height : Nat) : Polycube :=
  if height = 2 then Polycube.bumpyOne
  else if height = 3 then Polycube.bumpyTwo else Polycube.bumpyThree

def slabProblem (height : Nat) : List Voxel → Prop := problem (slabSmall height) (voxelSlab height)

def slabsStatement : Prop := ∀ height : Nat, 1 < height → LeanWang.CoREComplete (slabProblem height)

theorem slabSmall_not_tileable {height : Nat} (positive : 1 < height) :
    ¬ VoxelTileableBy (slabSmall height) (voxelSlab height) := by
  by_cases two : height = 2
  · subst height
    simpa [slabSmall] using Polycube.bumpyOne_not_tileable_slab_two
  by_cases three : height = 3
  · subst height
    simpa [slabSmall] using Polycube.bumpyTwo_not_tileable_slab_three
  intro h
  apply Polycube.bumpyThree_not_tileable_space
  apply voxel_space_tileable_of_slab (fun _ : Unit => Polycube.bumpyThree) (by omega : 0 < height)
  simpa [VoxelTileableBy,slabSmall,two,three] using h

end LeanTrominoes.TwoConnectedPolycubes
