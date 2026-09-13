/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeLayerAssembly
import LeanTrominoes.TilingTranslation

/-! # Translation of voxel tilings and horizontal recentering of slabs -/

namespace LeanTrominoes
namespace VoxelPlacement

def shift {ι : Type*} (offset : Voxel) (p : VoxelPlacement ι) : VoxelPlacement ι :=
  ⟨p.kind, p.symmetry, Voxel.add offset p.offset⟩

theorem shift_injective {ι : Type*} (offset : Voxel) :
    Function.Injective (shift (ι := ι) offset) := by
  intro a b h
  apply VoxelPlacement.ext
  · simpa only [shift] using congrArg (fun p : VoxelPlacement ι => p.kind) h
  · simpa only [shift] using congrArg (fun p : VoxelPlacement ι => p.symmetry) h
  · exact Voxel.add_left_injective offset (congrArg VoxelPlacement.offset h)

@[simp] theorem shift_cancel {ι : Type*} (offset : Voxel) (p : VoxelPlacement ι) :
    (p.shift (Voxel.sub ((0, 0), 0) offset)).shift offset = p := by
  apply VoxelPlacement.ext
  · rfl
  · rfl
  · simp [shift, Voxel.add, Voxel.sub, Cell.add, Cell.sub]

theorem mem_shift_cells {ι : Type*} (tiles : ι → Polycube)
    (offset : Voxel) (p : VoxelPlacement ι) (c : Voxel) :
    Voxel.add offset c ∈ (p.shift offset).cells tiles ↔ c ∈ p.cells tiles := by
  simp only [mem_cells_iff]
  constructor
  · rintro ⟨q, hq, he⟩
    refine ⟨q, hq, ?_⟩
    apply Voxel.add_left_injective offset
    simpa only [shift, Voxel.add, Cell.add, Int.add_assoc] using he
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    simp only [shift, Voxel.add, Cell.add, Int.add_assoc]

@[simp] theorem shift_toVoxel {ι : Type*} (offset : Cell) (p : Placement ι) :
    p.toVoxel.shift (offset, 0) = (p.shift offset).toVoxel := rfl

end VoxelPlacement

theorem IsVoxelTiling.recenter {ι : Type*} {tiles : ι → Polycube} {region : Set Voxel}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles region placements)
    (offset : Voxel) (invariant : ∀ c, Voxel.add offset c ∈ region ↔ c ∈ region) :
    IsVoxelTiling tiles region {p | p.shift offset ∈ placements} := by
  constructor
  · intro p hp c hc
    exact (invariant c).mp (tiling.tilesInside _ hp _
      ((VoxelPlacement.mem_shift_cells tiles offset p c).mpr hc))
  · intro c hc
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ :=
      tiling.uniqueCover (Voxel.add offset c) ((invariant c).mpr hc)
    let p := a.shift (Voxel.sub ((0, 0), 0) offset)
    have shifted : p.shift offset = a := VoxelPlacement.shift_cancel offset a
    have member : p.shift offset ∈ placements := shifted ▸ ha
    have pc : c ∈ p.cells tiles := by
      apply (VoxelPlacement.mem_shift_cells tiles offset p c).mp
      rwa [shifted]
    refine ⟨p, ⟨member, pc⟩, ?_⟩
    intro b hb
    apply VoxelPlacement.shift_injective offset
    rw [shifted]
    exact unique (b.shift offset)
      ⟨hb.1, (VoxelPlacement.mem_shift_cells tiles offset b c).mpr hb.2⟩

theorem IsVoxelTiling.recenter_slab {ι : Type*} {tiles : ι → Polycube} {height : Nat}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles (voxelSlab height) placements)
    (offset : Cell) :
    IsVoxelTiling tiles (voxelSlab height) {p | p.shift (offset, 0) ∈ placements} :=
  tiling.recenter (offset, 0) (by intro c; simp [voxelSlab, Voxel.add])

end LeanTrominoes
