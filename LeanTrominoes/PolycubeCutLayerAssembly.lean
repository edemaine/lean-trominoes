/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeLayerAssembly
import Mathlib.Data.Int.Interval

/-! # Assemble a slab from two compatible planar tilings at any layer cut -/

namespace LeanTrominoes

def Polycube.cutCapped (body cap : Polyomino) (cut height : Nat) : Polycube :=
  extrude body (Finset.Ico (0 : Int) cut) ∪ extrude cap (Finset.Ico (cut : Int) height)

theorem Placement.mem_toVoxel_cutCapped {ι : Type*} (body cap : ι → Polyomino)
    (cut height : Nat) (p : Placement ι) (c : Voxel) :
    c ∈ p.toVoxel.cells (fun i => Polycube.cutCapped (body i) (cap i) cut height) ↔
      (c.1 ∈ p.cells body ∧ 0 ≤ c.2 ∧ c.2 < cut) ∨
        (c.1 ∈ p.cells cap ∧ (cut : Int) ≤ c.2 ∧ c.2 < height) := by
  have distribute : p.toVoxel.cells (fun i => Polycube.cutCapped (body i) (cap i) cut height) =
      p.toVoxel.cells (fun i => Polycube.extrude (body i) (Finset.Ico (0 : Int) cut)) ∪
        p.toVoxel.cells (fun i => Polycube.extrude (cap i) (Finset.Ico (cut : Int) height)) := by
    simp [VoxelPlacement.cells,Polycube.cutCapped,Finset.image_union]
  rw [distribute,Finset.mem_union,Placement.mem_toVoxel_extrude,Placement.mem_toVoxel_extrude]
  simp

theorem voxel_slab_tiling_of_cut {ι : Type*} (body cap : ι → Polyomino)
    (cut height : Nat) (within : cut ≤ height) (placements : Set (Placement ι))
    (bodyTiling : IsTiling body Set.univ placements) (capTiling : IsTiling cap Set.univ placements) :
    IsVoxelTiling (fun i => Polycube.cutCapped (body i) (cap i) cut height)
      (voxelSlab height) (Placement.toVoxel '' placements) := by
  constructor
  · rintro _ ⟨p,hp,rfl⟩ c hc
    rcases (p.mem_toVoxel_cutCapped body cap cut height c).mp hc with h | h <;>
      change 0 ≤ c.2 ∧ c.2 < height <;> omega
  · intro c hc
    have bounds : 0 ≤ c.2 ∧ c.2 < height := hc
    by_cases middle : c.2 < cut
    · obtain ⟨p,⟨hp,hpc⟩,unique⟩ := bodyTiling.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel,⟨⟨p,hp,rfl⟩,
        (p.mem_toVoxel_cutCapped body cap cut height c).mpr (Or.inl ⟨hpc,bounds.1,middle⟩)⟩,?_⟩
      rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
      have cover : c.1 ∈ q.cells body := by
        rcases (q.mem_toVoxel_cutCapped body cap cut height c).mp hqc with h | h
        · exact h.1
        · omega
      exact congrArg Placement.toVoxel (unique q ⟨hq,cover⟩)
    · obtain ⟨p,⟨hp,hpc⟩,unique⟩ := capTiling.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel,⟨⟨p,hp,rfl⟩,
        (p.mem_toVoxel_cutCapped body cap cut height c).mpr (Or.inr ⟨hpc,by omega,bounds.2⟩)⟩,?_⟩
      rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
      have cover : c.1 ∈ q.cells cap := by
        rcases (q.mem_toVoxel_cutCapped body cap cut height c).mp hqc with h | h
        · omega
        · exact h.1
      exact congrArg Placement.toVoxel (unique q ⟨hq,cover⟩)

end LeanTrominoes
