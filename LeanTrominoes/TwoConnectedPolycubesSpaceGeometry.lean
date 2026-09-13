/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceRecovery
import LeanTrominoes.KeyedPolycubeSpaceForward
import LeanTrominoes.TwoConnectedPolycubes
import LeanTrominoes.Theorem55Geometry

/-! # Exact simulation by two connected polycubes in the full space -/

namespace LeanTrominoes.TwoConnectedPolycubes

open KeyedPeriodicComplement

theorem space_tileable_iff_tromino {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source) :
    VoxelTileable (spaceFamily n holes) Set.univ ↔ Tromino.I.Tileable source := by
  constructor
  · intro h
    exact (Theorem55.pair_tileable_iff hn period holes admissible source carrier).mp
      (planar_tileable_of_space hn period holes admissible h)
  · exact space_tileable_of_tromino (by omega) holes source carrier

theorem spaceProblem_iff_of_mask {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source)
    (input : List Voxel) (encoding : input.toFinset = spaceTile n holes) :
    spaceProblem input ↔ Tromino.I.Tileable source := by
  simp only [spaceProblem, problem, encoding, spaceTile_connected hn holes admissible, true_and]
  exact space_tileable_iff_tromino hn period holes admissible source carrier

end LeanTrominoes.TwoConnectedPolycubes
