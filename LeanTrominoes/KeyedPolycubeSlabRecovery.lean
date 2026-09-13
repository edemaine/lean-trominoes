/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSlabGrid
import LeanTrominoes.SquareGridTiling

/-! # Recover the planar simulation from the complete slab background grid -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem slab_grid_upper_cover {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (placements : Set (VoxelPlacement Bool))
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements) (c : Cell) :
    ∃ g ∈ placements, g.kind = true ∧ g.symmetry.flip = false ∧
      (c, 1) ∈ g.cells (slabFamily n holes) := by
  obtain ⟨p, hp, hc⟩ := (square_grid_tiling hn).exists_cover (Set.mem_univ c)
  refine ⟨(p.tag true).toVoxel, grid p hp, rfl, rfl, ?_⟩
  rw [slabFamily_eq_capped, Placement.mem_toVoxel_capped]
  exact Or.inr ⟨hc, rfl⟩

theorem slab_grid_upper_kind {n : Nat} (hn : 0 < n) (holes : Polyomino)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (c : Cell)
    (hc : (c, 1) ∈ p.cells (slabFamily n holes)) :
    p.kind = true ∧ p.symmetry.flip = false := by
  obtain ⟨g, hg, hk, hf, hgc⟩ := slab_grid_upper_cover hn holes placements grid c
  obtain ⟨q, _, unique⟩ := tiling.uniqueCover (c, 1) (by
    change 0 ≤ (1 : Int) ∧ (1 : Int) < 2
    decide)
  have he : p = g := (unique p ⟨hp, hc⟩).trans (unique g ⟨hg, hgc⟩).symm
  simpa only [he] using And.intro hk hf

/-- The cap grid excludes all placements whose original zero layer is at height one. -/
theorem slab_grid_height_zero {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) : p.offset.2 = 0 := by
  have horizontal := mixed_slab_horizontal hn holes p (tiling.tilesInside p hp)
  let c := Voxel.add p.offset (p.symmetry.act ((0, 0), 0))
  have hc : c ∈ p.cells (slabFamily n holes) :=
    (p.mem_cells_iff _ _).mpr ⟨((0, 0), 0), origin_mem_slabFamily hn holes admissible p.kind, rfl⟩
  have height : c.2 = p.offset.2 := by
    simp [c, Voxel.add, CubeSymmetry.act, horizontal, CubeSymmetry.cycle]
  have bounds := tiling.tilesInside p hp c hc
  change 0 ≤ c.2 ∧ c.2 < (2 : Int) at bounds
  have hz : p.offset.2 = 0 ∨ p.offset.2 = 1 := by omega
  rcases hz with hz | hz
  · exact hz
  · have hc' : (c.1, 1) ∈ p.cells (slabFamily n holes) := by
      have he : (c.1, 1) = c := Prod.ext rfl (by omega)
      rwa [he]
    obtain ⟨hk, hf⟩ := slab_grid_upper_kind (by omega : 0 < n) holes placements tiling grid p hp c.1 hc'
    simpa [hf] using mixed_background_height hn holes admissible p hk (tiling.tilesInside p hp)

theorem slab_grid_zero_slice {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements)
    (p : VoxelPlacement Bool) (hp : p ∈ placements) (c : Cell) :
    (c, 0) ∈ p.cells (slabFamily n holes) ↔ c ∈ p.toPlanar.cells (planarFamily n holes) := by
  have height := slab_grid_height_zero hn holes admissible placements tiling grid p hp
  cases hk : p.kind with
  | false =>
    simpa only [height, and_true] using small_zero_slice n holes p hk
      (mixed_slab_horizontal hn holes p (tiling.tilesInside p hp)) c
  | true =>
    have hf : p.symmetry.flip = false := by
      have h := mixed_background_height hn holes admissible p hk (tiling.tilesInside p hp)
      cases he : p.symmetry.flip <;> simp_all
    simpa only [hf, Bool.false_eq_true, ↓reduceIte] using
      background_zero_slice hn holes admissible p hk (tiling.tilesInside p hp) c

/-- Projecting the zero layer of a slab tiling with its complete cap grid
gives an exact planar tiling by the original P and Q. -/
theorem planar_tileable_of_slab_grid {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (grid : ∀ p ∈ gridPlacements n, (p.tag true).toVoxel ∈ placements) :
    Tileable (planarFamily n holes) Set.univ := by
  have slice := slab_grid_zero_slice hn holes admissible placements tiling grid
  refine ⟨VoxelPlacement.toPlanar '' placements, ?_, ?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨p, ⟨hp, hc⟩, unique⟩ := tiling.uniqueCover (c, 0) (by
      change 0 ≤ (0 : Int) ∧ (0 : Int) < 2
      decide)
    refine ⟨p.toPlanar, ⟨⟨p, hp, rfl⟩, (slice p hp c).mp hc⟩, ?_⟩
    rintro _ ⟨⟨q, hq, rfl⟩, hqc⟩
    exact congrArg VoxelPlacement.toPlanar (unique q ⟨hq, (slice q hq c).mpr hqc⟩)

theorem planar_tileable_of_slab_seed {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (slabFamily n holes) (voxelSlab 2) placements)
    (seed : slabReference ∈ placements) : Tileable (planarFamily n holes) Set.univ := by
  obtain ⟨ps, ht, grid⟩ := slab_exists_tiling_with_grid hn period holes admissible placements tiling seed
  exact planar_tileable_of_slab_grid hn holes admissible ps ht grid

end LeanTrominoes.KeyedPeriodicComplement
