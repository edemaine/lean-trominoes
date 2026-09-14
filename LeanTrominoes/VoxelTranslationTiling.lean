/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTiling

/-! # Exact tilings with restricted orientations -/

namespace LeanTrominoes

/-- Only placements satisfying `allowed` may be used. -/
def VoxelTileableWith {ι : Type*} (tiles : ι → Polycube) (region : Set Voxel)
    (allowed : VoxelPlacement ι → Prop) : Prop :=
  ∃ placements, IsVoxelTiling tiles region placements ∧ ∀ p ∈ placements, allowed p

/-- Every tile is placed by translation alone. -/
def VoxelTranslationTileable {ι : Type*} (tiles : ι → Polycube) (region : Set Voxel) : Prop :=
  VoxelTileableWith tiles region (fun p => p.symmetry = CubeSymmetry.identity)

theorem VoxelTileableWith.tileable {ι : Type*} {tiles : ι → Polycube} {region : Set Voxel}
    {allowed : VoxelPlacement ι → Prop} (h : VoxelTileableWith tiles region allowed) : VoxelTileable tiles region :=
  ⟨h.choose,h.choose_spec.1⟩

/-- Replacing placements by copies with identical footprints preserves exact tilings.
The replacement need not be injective on unused or empty placements. -/
theorem IsVoxelTiling.map_cells {ι κ : Type*} {tiles : ι → Polycube} {other : κ → Polycube}
    {region : Set Voxel} {placements : Set (VoxelPlacement ι)}
    (h : IsVoxelTiling tiles region placements) (f : VoxelPlacement ι → VoxelPlacement κ)
    (same : ∀ p ∈ placements, (f p).cells other = p.cells tiles) :
    IsVoxelTiling other region (f '' placements) := by
  constructor
  · rintro q ⟨p,hp,rfl⟩ c hc
    exact h.tilesInside p hp c ((same p hp) ▸ hc)
  · intro c hc
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := h.uniqueCover c hc
    refine ⟨f p,⟨⟨p,hp,rfl⟩,by rwa [same p hp]⟩,?_⟩
    rintro q ⟨⟨r,hr,rfl⟩,hrc⟩
    exact congrArg f (unique r ⟨hr,by rwa [← same r hr]⟩)

theorem VoxelTileableWith.map_cells {ι κ : Type*} {tiles : ι → Polycube} {other : κ → Polycube}
    {region : Set Voxel} {allowed : VoxelPlacement ι → Prop} {allowedOther : VoxelPlacement κ → Prop}
    (h : VoxelTileableWith tiles region allowed) (f : VoxelPlacement ι → VoxelPlacement κ)
    (same : ∀ p, allowed p → (f p).cells other = p.cells tiles)
    (legal : ∀ p, allowed p → allowedOther (f p)) :
    VoxelTileableWith other region allowedOther := by
  obtain ⟨placements,tiling,allowed⟩ := h
  refine ⟨f '' placements,tiling.map_cells f (fun p hp => same p (allowed p hp)),?_⟩
  rintro q ⟨p,hp,rfl⟩
  exact legal p (allowed p hp)

end LeanTrominoes
