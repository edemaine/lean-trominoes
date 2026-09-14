/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubeGeometry
import LeanTrominoes.VoxelRestrictedStack
import LeanTrominoes.VoxelBandAssembly
import LeanTrominoes.KeyedPolycubeForward
import LeanTrominoes.KeyedPolycubeTallSlabForward
import LeanTrominoes.KeyedPolycubeSpaceForward

/-! # Connected-polycube forward constructions preserve allowed orientations -/

namespace LeanTrominoes.ThreeTranslationPolycubes
open KeyedPeriodicComplement

private theorem compatible_layers {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    ∃ placements,
      IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ placements ∧
      IsTiling (pairTiles ∅ (square n)) Set.univ placements ∧
      ∀ p ∈ Placement.toVoxel '' placements, Allowed p := by
  obtain ⟨ps,ht⟩ := h
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
  refine ⟨placements,lower,upper,?_⟩
  rintro p ⟨q,hq,rfl⟩
  refine ⟨rfl,rfl,?_⟩
  intro kind
  have member : q.untag ∈ gridPlacements n := by
    simpa [placements,pairPlacements,show q.kind = true from kind] using hq
  exact member.1

theorem slab_two_restricted_of_holes {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    VoxelTileableWith (Polycube.pairTiles Polycube.bumpyOne (slabTile n holes)) (voxelSlab 2) Allowed := by
  obtain ⟨placements,lower,upper,legal⟩ := compatible_layers hn holes h
  have assembled := voxel_slab_tiling_of_layers
    (pairTiles PlusRefinement.bumpy (tile n holes)) (pairTiles ∅ (square n)) placements lower upper
  have eq : (fun i => Polycube.capped (pairTiles PlusRefinement.bumpy (tile n holes) i)
      (pairTiles ∅ (square n) i) {0} 1) = Polycube.pairTiles Polycube.bumpyOne (slabTile n holes) := by
    funext i
    cases i <;> simp [pairTiles,Polycube.pairTiles,Polycube.capped,Polycube.bumpyOne,slabTile,Polycube.extrude]
  rw [eq] at assembled
  exact ⟨_,assembled,legal⟩

theorem tall_slab_restricted_of_holes {height n : Nat} (hh : 3 ≤ height) (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    VoxelTileableWith (tallSlabFamily height n holes) (voxelSlab height) Allowed := by
  obtain ⟨placements,lower,upper,legal⟩ := compatible_layers hn holes h
  have assembled := voxel_slab_tiling_of_cut
    (pairTiles PlusRefinement.bumpy (tile n holes)) (pairTiles ∅ (square n))
    (slabBodyHeight height) height (by have := slabBodyHeight_bounds hh; omega) placements lower upper
  have eq : (fun i => Polycube.cutCapped (pairTiles PlusRefinement.bumpy (tile n holes) i)
      (pairTiles ∅ (square n) i) (slabBodyHeight height) height) = tallSlabFamily height n holes := by
    funext i
    cases i <;> simp [pairTiles,Polycube.pairTiles,Polycube.cutCapped,tallSlabFamily,tallSlabTile,
      slabSmall_eq_extrude hh,Polycube.extrude]
  rw [eq] at assembled
  exact ⟨_,assembled,legal⟩

theorem space_restricted_of_holes {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (h : TileableBy PlusRefinement.bumpy (holesRegion n holes)) :
    VoxelTileableWith (Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes)) Set.univ Allowed := by
  obtain ⟨placements,lower,upper,legal⟩ := compatible_layers hn holes h
  have band := voxel_band_tiling_of_layers
    (pairTiles PlusRefinement.bumpy (tile n holes)) (pairTiles ∅ (square n)) placements lower upper
  have assembled := voxel_space_tileableWith_of_band _ _ band Allowed legal (fun _ _ h => h)
  have eq : (fun i => Polycube.solidCapped (pairTiles PlusRefinement.bumpy (tile n holes) i)
      (pairTiles ∅ (square n) i)) = Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes) := by
    funext i
    cases i <;> simp [pairTiles,Polycube.pairTiles,Polycube.solidCapped,Polycube.bumpyThree,spaceTile,Polycube.extrude]
  rw [eq] at assembled
  exact assembled

end LeanTrominoes.ThreeTranslationPolycubes
