/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity
import LeanTrominoes.PolycubePair
import LeanWang.CoRE

/-! # Targets for tiling with two connected polycubes

These are target definitions. `TwoConnectedPolycubesSlabProof` and
`TwoConnectedPolycubesSpaceProof` supply the completeness proofs. The fixed
space tile has 45 voxels; the first slab target uses the fixed 15-voxel tile.
Inputs give the second tile explicitly, and disconnected or empty inputs
are rejected by the face-connectivity requirement.
-/

namespace LeanTrominoes.TwoConnectedPolycubes

def problem (small : Polycube) (region : Set Voxel) (input : List Voxel) : Prop :=
  Polycube.IsConnected input.toFinset ∧
    VoxelTileable (Polycube.pairTiles small input.toFinset) region

def spaceProblem : List Voxel → Prop := problem Polycube.bumpyThree Set.univ

def slabTwoProblem : List Voxel → Prop := problem Polycube.bumpyOne (voxelSlab 2)

def spaceStatement : Prop := LeanWang.CoREComplete spaceProblem

def slabTwoStatement : Prop := LeanWang.CoREComplete slabTwoProblem

end LeanTrominoes.TwoConnectedPolycubes
