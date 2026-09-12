/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeHorizontalSlice

/-! # Assemble two planar layers into an exact slab tiling

Both layers use the same planar placement records, with possibly empty
shapes in either layer. In the reduction, P has an empty top layer and Q
has a square cap.
-/

namespace LeanTrominoes

namespace Placement

def toVoxel {ι : Type*} (p : Placement ι) : VoxelPlacement ι :=
  ⟨p.kind, ⟨p.symmetry, false, 0⟩, (p.offset, 0)⟩

@[simp] theorem toPlanar_toVoxel {ι : Type*} (p : Placement ι) : p.toVoxel.toPlanar = p := rfl

theorem toVoxel_injective {ι : Type*} : Function.Injective (@toVoxel ι) :=
  Function.LeftInverse.injective toPlanar_toVoxel

theorem mem_toVoxel_extrude {ι : Type*} (tiles : ι → Polyomino) (layers : Finset Int)
    (p : Placement ι) (c : Voxel) :
    c ∈ p.toVoxel.cells (fun i => Polycube.extrude (tiles i) layers) ↔
      c.1 ∈ p.cells tiles ∧ c.2 ∈ layers := by
  simp only [VoxelPlacement.mem_cells_iff, Polycube.mem_extrude, Placement.mem_cells_iff]
  constructor
  · rintro ⟨⟨source, z⟩, ⟨hs, hz⟩, he⟩
    have he' : Cell.add p.offset (p.symmetry.act source) = c.1 ∧ z = c.2 := by
      simpa [toVoxel, CubeSymmetry.act, CubeSymmetry.cycle, Voxel.add] using
        (Prod.mk.inj he)
    exact ⟨⟨source, hs, he'.1⟩, he'.2 ▸ hz⟩
  · rintro ⟨⟨source, hs, he⟩, hz⟩
    refine ⟨(source, c.2), ⟨hs, hz⟩, ?_⟩
    change (Cell.add p.offset (p.symmetry.act source), 0 + c.2) = c
    exact Prod.ext he (Int.zero_add _)

theorem mem_toVoxel_capped {ι : Type*} (bottom top : ι → Polyomino)
    (p : Placement ι) (c : Voxel) :
    c ∈ p.toVoxel.cells (fun i => Polycube.capped (bottom i) (top i) {0} 1) ↔
      (c.1 ∈ p.cells bottom ∧ c.2 = 0) ∨ (c.1 ∈ p.cells top ∧ c.2 = 1) := by
  have distribute :
      p.toVoxel.cells (fun i => Polycube.capped (bottom i) (top i) {0} 1) =
        p.toVoxel.cells (fun i => Polycube.extrude (bottom i) {0}) ∪
          p.toVoxel.cells (fun i => Polycube.extrude (top i) {1}) := by
    simp [VoxelPlacement.cells, Polycube.capped, Finset.image_union]
  rw [distribute, Finset.mem_union, mem_toVoxel_extrude, mem_toVoxel_extrude]
  simp

end Placement

/-- Compatible exact tilings of the two layers assemble into an exact slab tiling. -/
theorem voxel_slab_tiling_of_layers {ι : Type*} (bottom top : ι → Polyomino)
    (placements : Set (Placement ι))
    (lower : IsTiling bottom Set.univ placements)
    (upper : IsTiling top Set.univ placements) :
    IsVoxelTiling (fun i => Polycube.capped (bottom i) (top i) {0} 1) (voxelSlab 2)
      (Placement.toVoxel '' placements) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩ c hc
    rcases (p.mem_toVoxel_capped bottom top c).mp hc with ⟨_, hz⟩ | ⟨_, hz⟩ <;>
      change 0 ≤ c.2 ∧ c.2 < (2 : Int) <;> omega
  · intro c hc
    have hz : c.2 = 0 ∨ c.2 = 1 := by
      change 0 ≤ c.2 ∧ c.2 < (2 : Int) at hc
      omega
    rcases hz with hz | hz
    · obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := lower.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel, ⟨⟨p, hp, rfl⟩, ?_⟩, ?_⟩
      · exact (p.mem_toVoxel_capped bottom top c).mpr (Or.inl ⟨hpc, hz⟩)
      · rintro _ ⟨⟨q, hq, rfl⟩, hqc⟩
        have hqc' : c.1 ∈ q.cells bottom := by
          simpa [hz] using (q.mem_toVoxel_capped bottom top c).mp hqc
        exact congrArg Placement.toVoxel (unique q ⟨hq, hqc'⟩)
    · obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := upper.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel, ⟨⟨p, hp, rfl⟩, ?_⟩, ?_⟩
      · exact (p.mem_toVoxel_capped bottom top c).mpr (Or.inr ⟨hpc, hz⟩)
      · rintro _ ⟨⟨q, hq, rfl⟩, hqc⟩
        have hqc' : c.1 ∈ q.cells top := by
          simpa [hz] using (q.mem_toVoxel_capped bottom top c).mp hqc
        exact congrArg Placement.toVoxel (unique q ⟨hq, hqc'⟩)

end LeanTrominoes
