/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeBasic

/-! # Exact tilings in three dimensions -/

namespace LeanTrominoes

structure IsVoxelTiling {ι : Type*} (tiles : ι → Polycube)
    (region : Set Voxel) (placements : Set (VoxelPlacement ι)) : Prop where
  tilesInside : ∀ p ∈ placements, ∀ c ∈ p.cells tiles, c ∈ region
  uniqueCover : ∀ c ∈ region,
    ∃! p : VoxelPlacement ι, p ∈ placements ∧ c ∈ p.cells tiles

namespace IsVoxelTiling

theorem exists_cover {ι : Type*} {tiles : ι → Polycube}
    {region : Set Voxel} {placements : Set (VoxelPlacement ι)}
    (tiling : IsVoxelTiling tiles region placements) {c : Voxel} (hc : c ∈ region) :
    ∃ p ∈ placements, c ∈ p.cells tiles := by
  obtain ⟨p, ⟨hp, hpc⟩, _⟩ := tiling.uniqueCover c hc
  exact ⟨p, hp, hpc⟩

theorem disjoint_cells {ι : Type*} {tiles : ι → Polycube}
    {region : Set Voxel} {placements : Set (VoxelPlacement ι)}
    (tiling : IsVoxelTiling tiles region placements)
    {p q : VoxelPlacement ι} (hp : p ∈ placements) (hq : q ∈ placements)
    (hne : p ≠ q) : Disjoint (p.cells tiles) (q.cells tiles) := by
  rw [Finset.disjoint_left]
  intro c hpc hqc
  obtain ⟨r, _, unique⟩ := tiling.uniqueCover c (tiling.tilesInside p hp c hpc)
  exact hne ((unique p ⟨hp, hpc⟩).trans (unique q ⟨hq, hqc⟩).symm)

end IsVoxelTiling

def VoxelTileable {ι : Type*} (tiles : ι → Polycube) (region : Set Voxel) : Prop :=
  ∃ placements, IsVoxelTiling tiles region placements

def VoxelTileableBy (tile : Polycube) (region : Set Voxel) : Prop :=
  VoxelTileable (fun _ : Unit => tile) region

/-- The slab has voxel layers `0, …, height - 1`. -/
def voxelSlab (height : Nat) : Set Voxel := {c | 0 ≤ c.2 ∧ c.2 < height}

end LeanTrominoes
