/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.VoxelTranslationTiling
import LeanTrominoes.ThreeTranslationPolyominoes
import LeanTrominoes.TwoConnectedPolycubesSlabs

/-! # Corollary 5.9: three connected polycubes with translations only -/

namespace LeanTrominoes.ThreeTranslationPolycubes

def fixed (layers : Finset Int) (vertical : Bool) : Polycube :=
  Polycube.extrude (ThreeTranslationPolyominoes.fixed vertical) layers

def tiles (layers : Finset Int) (q : Polycube) : Option Bool → Polycube
  | none => q
  | some vertical => fixed layers vertical

def problem (layers : Finset Int) (region : Set Voxel) (input : List Voxel) : Prop :=
  Polycube.IsConnected input.toFinset ∧ VoxelTranslationTileable (tiles layers input.toFinset) region

def slabLayers (height : Nat) : Finset Int :=
  if height = 2 then {0} else if height = 3 then {0,1} else {0,1,2}

def spaceProblem : List Voxel → Prop := problem {0,1,2} Set.univ

def slabProblem (height : Nat) : List Voxel → Prop := problem (slabLayers height) (voxelSlab height)

def spaceStatement : Prop := LeanWang.CoREComplete spaceProblem

def slabsStatement : Prop := ∀ height : Nat, 1 < height → LeanWang.CoREComplete (slabProblem height)

def statement : Prop := spaceStatement ∧ slabsStatement

/-- The forward construction uses horizontal placements and never turns Q. -/
def Allowed (p : VoxelPlacement Bool) : Prop :=
  p.symmetry.axis = 0 ∧ p.symmetry.flip = false ∧ (p.kind = true → p.symmetry.planar = .identity)

end LeanTrominoes.ThreeTranslationPolycubes
