/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeCutLayerAssembly
import LeanTrominoes.PolycubePair
import LeanTrominoes.KeyedPolycubeTallSlabConnected
import LeanTrominoes.SquareGridTiling
import LeanTrominoes.TilingPair
import LeanTrominoes.BumpyTrominoRefinement

/-! # Forward construction for the arbitrary taller slabs

The bottom layer is the established P/Q tiling. The upper layer consists
exactly of Q's square caps at the same canonical offsets.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem tall_slab_tileable_of_holes {height n : Nat} (hh : 3 ≤ height) (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    VoxelTileable (tallSlabFamily height n holes) (voxelSlab height) := by
  obtain ⟨ps, ht⟩ := h
  let placements := pairPlacements ps (gridPlacements n)
  have lower := isTiling_pair_of_complement PlusRefinement.bumpy (tile n holes)
    (holesRegion n holes) ps (gridPlacements n) ht (grid_tiling hn holes)
  have emptyTiling : IsTiling (fun _ : Unit => (∅ : Polyomino)) ∅ ps := by
    constructor
    · intro p _ c hc
      simp [Placement.cells] at hc
    · intro c hc
      exact False.elim hc
  have upper : IsTiling (pairTiles ∅ (square n)) Set.univ placements :=
    isTiling_pair_of_complement ∅ (square n) ∅ ps (gridPlacements n) emptyTiling
      (by simpa using square_grid_tiling hn)
  have assembled := voxel_slab_tiling_of_cut
    (pairTiles PlusRefinement.bumpy (tile n holes)) (pairTiles ∅ (square n))
    (slabBodyHeight height) height (by have := slabBodyHeight_bounds hh; omega) placements lower upper
  have tiles : (fun i => Polycube.cutCapped
      (pairTiles PlusRefinement.bumpy (tile n holes) i) (pairTiles ∅ (square n) i) (slabBodyHeight height) height) =
      tallSlabFamily height n holes := by
    funext i
    cases i <;> simp [pairTiles, Polycube.pairTiles, Polycube.cutCapped,
      tallSlabFamily, tallSlabTile, slabSmall_eq_extrude hh, Polycube.extrude]
  rw [tiles] at assembled
  exact ⟨Placement.toVoxel '' placements, assembled⟩

/-- Every I-tromino tiling of the source gives a tiling by the two slab polycubes. -/
theorem tall_slab_tileable_of_tromino {height n : Nat} (hh : 3 ≤ height) (hn : 0 < n) (holes : Polyomino)
    (source : Set Cell) (mask : holesRegion n holes = PlusRefinement.region source)
    (h : Tromino.I.Tileable source) :
    VoxelTileable (tallSlabFamily height n holes) (voxelSlab height) := by
  apply tall_slab_tileable_of_holes hh hn holes
  rw [mask]
  exact (PlusRefinement.bumpy_tileable_refinement_iff source).mpr h

end LeanTrominoes.KeyedPeriodicComplement
