/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabRecovery
import LeanTrominoes.KeyedPolycubeTallSlabForward
import LeanTrominoes.TwoConnectedPolycubes
import LeanTrominoes.Theorem55Geometry

/-! # Exact simulation by two connected polycubes in the every taller slab -/

namespace LeanTrominoes.TwoConnectedPolycubes

open KeyedPeriodicComplement

theorem tall_slab_tileable_iff_tromino {height n : Nat} (hh : 3 ≤ height) (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source) :
    VoxelTileable (tallSlabFamily height n holes) (voxelSlab height) ↔ Tromino.I.Tileable source := by
  constructor
  · intro h
    exact (Theorem55.pair_tileable_iff hn period holes admissible source carrier).mp
      (planar_tileable_of_tall_slab hh wide hn period holes admissible h)
  · exact tall_slab_tileable_of_tromino hh (by omega) holes source carrier

theorem slabProblem_iff_of_mask {height n : Nat} (hh : 3 ≤ height) (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (source : Set Cell)
    (carrier : holesRegion n holes = PlusRefinement.region source)
    (input : List Voxel) (encoding : input.toFinset = tallSlabTile height n holes) :
    slabProblem height input ↔ Tromino.I.Tileable source := by
  simp only [slabProblem, problem, encoding, tallSlabTile_connected hh hn holes admissible, true_and]
  exact tall_slab_tileable_iff_tromino hh wide hn period holes admissible source carrier

end LeanTrominoes.TwoConnectedPolycubes
