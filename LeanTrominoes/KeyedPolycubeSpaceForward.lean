/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSolidCapAssembly
import LeanTrominoes.PolycubePair
import LeanTrominoes.KeyedPolycubeSpaceCanonical
import LeanTrominoes.SquareGridTiling
import LeanTrominoes.TilingPair
import LeanTrominoes.BumpyTrominoRefinement

/-! # Forward construction for the full space

The three body layers carry the established P/Q tiling, with square caps
at the same canonical offsets. Repeat these five-layer bands vertically.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem space_tileable_of_holes {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    VoxelTileable (Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes)) Set.univ := by
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
  have assembled := voxel_space_tileable_of_layers
    (pairTiles PlusRefinement.bumpy (tile n holes)) (pairTiles ∅ (square n))
    placements lower upper
  have tiles : (fun i => Polycube.solidCapped
      (pairTiles PlusRefinement.bumpy (tile n holes) i) (pairTiles ∅ (square n) i)) =
      Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes) := by
    funext i
    cases i <;> simp [pairTiles, Polycube.pairTiles, Polycube.solidCapped,
      Polycube.bumpyThree, spaceTile, Polycube.extrude]
  rw [tiles] at assembled
  exact assembled

/-- Every I-tromino tiling of the source gives a tiling by the two full-space polycubes. -/
theorem space_tileable_of_tromino {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (source : Set Cell) (mask : holesRegion n holes = PlusRefinement.region source)
    (h : Tromino.I.Tileable source) :
    VoxelTileable (Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes)) Set.univ := by
  apply space_tileable_of_holes hn holes
  rw [mask]
  exact (PlusRefinement.bumpy_tileable_refinement_iff source).mpr h

end LeanTrominoes.KeyedPeriodicComplement
