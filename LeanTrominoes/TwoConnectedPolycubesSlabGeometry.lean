/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSlabNormalization
import LeanTrominoes.KeyedPolycubeForward
import LeanTrominoes.TwoConnectedPolycubes
import LeanTrominoes.Theorem55Geometry

/-! # Exact simulation by two connected polycubes in the height-two slab -/

namespace LeanTrominoes.TwoConnectedPolycubes

open KeyedPeriodicComplement

theorem slab_tileable_iff_tromino {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source) :
    VoxelTileable (slabFamily n holes) (voxelSlab 2) ↔ Tromino.I.Tileable source := by
  constructor
  · intro h
    exact (Theorem55.pair_tileable_iff hn period holes admissible source carrier).mp
      (planar_tileable_of_slab hn period holes admissible h)
  · exact slab_tileable_of_tromino (by omega) holes source carrier

theorem slabTwoProblem_iff_of_mask {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source)
    (input : List Voxel) (encoding : input.toFinset = slabTile n holes) :
    slabTwoProblem input ↔ Tromino.I.Tileable source := by
  simp only [slabTwoProblem, problem, encoding, slabTile_connected hn holes admissible, true_and]
  exact slab_tileable_iff_tromino hn period holes admissible source carrier

end LeanTrominoes.TwoConnectedPolycubes
