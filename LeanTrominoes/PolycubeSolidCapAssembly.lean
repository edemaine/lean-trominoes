/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeLayerAssembly
import LeanTrominoes.PolycubePeriodicStack

/-! # Compatible planar tilings assemble into periodically repeated solid-cap bands -/

namespace LeanTrominoes

def Polycube.solidCapped (body cap : Polyomino) : Polycube :=
  extrude body {0,1,2} ∪ extrude cap {-1,3}

theorem Placement.mem_toVoxel_solidCapped {ι : Type*} (body cap : ι → Polyomino)
    (p : Placement ι) (c : Voxel) :
    c ∈ p.toVoxel.cells (fun i => Polycube.solidCapped (body i) (cap i)) ↔
      (c.1 ∈ p.cells body ∧ 0 ≤ c.2 ∧ c.2 ≤ 2) ∨
        (c.1 ∈ p.cells cap ∧ (c.2 = -1 ∨ c.2 = 3)) := by
  have distribute : p.toVoxel.cells (fun i => Polycube.solidCapped (body i) (cap i)) =
      p.toVoxel.cells (fun i => Polycube.extrude (body i) {0,1,2}) ∪
        p.toVoxel.cells (fun i => Polycube.extrude (cap i) {-1,3}) := by
    simp [VoxelPlacement.cells,Polycube.solidCapped,Finset.image_union]
  rw [distribute,Finset.mem_union,Placement.mem_toVoxel_extrude,Placement.mem_toVoxel_extrude]
  have levels : c.2 ∈ ({0,1,2} : Finset Int) ↔ 0 ≤ c.2 ∧ c.2 ≤ 2 := by simp; omega
  simp [levels]

theorem voxel_space_tileable_of_layers {ι : Type*} (body cap : ι → Polyomino)
    (placements : Set (Placement ι))
    (bodyTiling : IsTiling body Set.univ placements)
    (capTiling : IsTiling cap Set.univ placements) :
    VoxelTileable (fun i => Polycube.solidCapped (body i) (cap i)) Set.univ := by
  apply voxel_space_tileable_of_band _ (Placement.toVoxel '' placements)
  constructor
  · rintro _ ⟨p,hp,rfl⟩ c hc
    rcases (p.mem_toVoxel_solidCapped body cap c).mp hc with h | h <;>
      change -1 ≤ c.2 ∧ c.2 ≤ 3 <;> omega
  · intro c hc
    have bounds : -1 ≤ c.2 ∧ c.2 ≤ 3 := hc
    by_cases middle : 0 ≤ c.2 ∧ c.2 ≤ 2
    · obtain ⟨p,⟨hp,hpc⟩,unique⟩ := bodyTiling.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel,⟨⟨p,hp,rfl⟩,(p.mem_toVoxel_solidCapped body cap c).mpr (Or.inl ⟨hpc,middle⟩)⟩,?_⟩
      rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
      have cover : c.1 ∈ q.cells body := by
        rcases (q.mem_toVoxel_solidCapped body cap c).mp hqc with h | h
        · exact h.1
        · omega
      exact congrArg Placement.toVoxel (unique q ⟨hq,cover⟩)
    · have ends : c.2 = -1 ∨ c.2 = 3 := by omega
      obtain ⟨p,⟨hp,hpc⟩,unique⟩ := capTiling.uniqueCover c.1 (Set.mem_univ _)
      refine ⟨p.toVoxel,⟨⟨p,hp,rfl⟩,(p.mem_toVoxel_solidCapped body cap c).mpr (Or.inr ⟨hpc,ends⟩)⟩,?_⟩
      rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
      have cover : c.1 ∈ q.cells cap := by
        rcases (q.mem_toVoxel_solidCapped body cap c).mp hqc with h | h
        · exact False.elim (middle h.2)
        · exact h.1
      exact congrArg Placement.toVoxel (unique q ⟨hq,cover⟩)

end LeanTrominoes
