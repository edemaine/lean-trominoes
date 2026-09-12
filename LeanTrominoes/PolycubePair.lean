/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTiling

/-! # Mixed tilings must use the background tile -/

namespace LeanTrominoes

def Polycube.pairTiles (p q : Polycube) (kind : Bool) : Polycube := if kind then q else p

namespace VoxelPlacement

def tag (kind : Bool) (p : VoxelPlacement Unit) : VoxelPlacement Bool :=
  ⟨kind, p.symmetry, p.offset⟩

def untag (p : VoxelPlacement Bool) : VoxelPlacement Unit := ⟨(), p.symmetry, p.offset⟩

@[simp] theorem untag_tag (kind : Bool) (p : VoxelPlacement Unit) : (p.tag kind).untag = p := by
  apply VoxelPlacement.ext
  · exact Subsingleton.elim _ _
  · rfl
  · rfl

@[simp] theorem tag_untag (p : VoxelPlacement Bool) : p.untag.tag p.kind = p := rfl

end VoxelPlacement

theorem voxel_right_tile_occurs (p q : Polycube) (region : Set Voxel)
    (placements : Set (VoxelPlacement Bool))
    (tiling : IsVoxelTiling (Polycube.pairTiles p q) region placements)
    (obstruction : ¬ VoxelTileableBy p region) : ∃ a ∈ placements, a.kind = true := by
  classical
  by_contra none
  have left (a : VoxelPlacement Bool) (ha : a ∈ placements) : a.kind = false := by
    cases hk : a.kind
    · rfl
    · exact False.elim (none ⟨a, ha, hk⟩)
  apply obstruction
  refine ⟨{a | a.tag false ∈ placements}, ?_, ?_⟩
  · intro a ha c hc
    exact tiling.tilesInside (a.tag false) ha c hc
  · intro c hc
    obtain ⟨a, ⟨ha, hca⟩, unique⟩ := tiling.uniqueCover c hc
    have hk := left a ha
    have tagged : a.untag.tag false = a := by rw [← hk, VoxelPlacement.tag_untag]
    have covers : c ∈ a.untag.cells (fun _ => p) := by
      simpa [VoxelPlacement.cells, VoxelPlacement.untag, Polycube.pairTiles, hk] using hca
    refine ⟨a.untag, ⟨?_, covers⟩, ?_⟩
    · change a.untag.tag false ∈ placements
      rwa [tagged]
    · rintro other ⟨ho, hco⟩
      have he := unique (other.tag false) ⟨ho, hco⟩
      simpa only [VoxelPlacement.untag_tag] using congrArg VoxelPlacement.untag he

end LeanTrominoes
