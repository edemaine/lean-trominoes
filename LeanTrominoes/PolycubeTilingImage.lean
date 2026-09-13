/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTiling

/-! # Replacing placement records without changing their occupied cells -/

namespace LeanTrominoes.IsVoxelTiling

theorem image {ι : Type*} {tiles : ι → Polycube} {region : Set Voxel}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles region placements)
    (f : VoxelPlacement ι → VoxelPlacement ι)
    (cells : ∀ p, (f p).cells tiles = p.cells tiles) :
    IsVoxelTiling tiles region (f '' placements) := by
  constructor
  · rintro _ ⟨p,hp,rfl⟩ c hc
    exact tiling.tilesInside p hp c (by rwa [cells] at hc)
  · intro c hc
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := tiling.uniqueCover c hc
    refine ⟨f p,⟨⟨p,hp,rfl⟩,by rwa [cells]⟩,?_⟩
    rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
    have eq := unique q ⟨hq,by rwa [cells] at hqc⟩
    exact congrArg f eq

end LeanTrominoes.IsVoxelTiling
