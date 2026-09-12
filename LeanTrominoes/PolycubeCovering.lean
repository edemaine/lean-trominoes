/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTiling

/-! # Finite covering candidates and translation of local obstructions -/

namespace LeanTrominoes.VoxelPlacement

/-- Inverse coordinates avoid constructing and deduplicating an image finset. -/
theorem mem_cells_inverse {ι : Type*} (tiles : ι → Polycube)
    (p : VoxelPlacement ι) (c : Voxel) :
    c ∈ p.cells tiles ↔ p.symmetry.inverseAct (Voxel.sub c p.offset) ∈ tiles p.kind := by
  rw [mem_cells_iff]
  constructor
  · rintro ⟨source, hs, rfl⟩
    simpa [Voxel.sub, Voxel.add, Cell.sub, Cell.add] using hs
  · intro h
    refine ⟨p.symmetry.inverseAct (Voxel.sub c p.offset), h, ?_⟩
    rw [CubeSymmetry.act_inverse_act]
    rcases c with ⟨⟨x, y⟩, z⟩
    simp [Voxel.add, Voxel.sub, Cell.add, Cell.sub]

def covering (target : Voxel) (s : CubeSymmetry) (source : Voxel) :
    VoxelPlacement Unit := ⟨(), s, Voxel.sub target (s.act source)⟩

def coveringPlacements (tile : Polycube) (target : Voxel) :
    Finset (VoxelPlacement Unit) :=
  Finset.univ.biUnion fun s => tile.image (covering target s)

theorem mem_coveringPlacements (tile : Polycube) (p : VoxelPlacement Unit)
    (target : Voxel) :
    p ∈ coveringPlacements tile target ↔ target ∈ p.cells (fun _ => tile) := by
  simp only [coveringPlacements, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, mem_cells_iff]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    exact ⟨c, hc, Voxel.sub_add _ _⟩
  · rintro ⟨c, hc, he⟩
    refine ⟨p.symmetry, c, hc, ?_⟩
    apply VoxelPlacement.ext
    · exact Subsingleton.elim _ _
    · rfl
    · simp only [Voxel.add, Cell.add, Prod.ext_iff] at he
      simp only [covering, Voxel.sub, Cell.sub, Prod.ext_iff]
      exact ⟨⟨by omega, by omega⟩, by omega⟩

def reference (s : CubeSymmetry) : VoxelPlacement Unit := ⟨(), s, ((0, 0), 0)⟩

def relative {ι : Type*} (origin : Voxel) (p : VoxelPlacement ι) : VoxelPlacement ι :=
  {p with offset := Voxel.sub p.offset origin}

theorem mem_relative {ι : Type*} (tiles : ι → Polycube) (origin c : Voxel)
    (p : VoxelPlacement ι) :
    c ∈ (relative origin p).cells tiles ↔ Voxel.add origin c ∈ p.cells tiles := by
  simp only [mem_cells_iff]
  constructor <;> rintro ⟨source, hs, he⟩ <;> refine ⟨source, hs, ?_⟩ <;>
    simp only [relative, Voxel.add, Voxel.sub, Cell.add, Cell.sub, Prod.ext_iff] at he ⊢ <;>
    exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem relative_self (p : VoxelPlacement Unit) :
    relative p.offset p = reference p.symmetry := by
  apply VoxelPlacement.ext
  · exact Subsingleton.elim _ _
  · rfl
  · simp [relative, reference, Voxel.sub, Cell.sub]

theorem disjoint_relative {ι : Type*} (tiles : ι → Polycube)
    (origin : Voxel) (p q : VoxelPlacement ι)
    (h : Disjoint (p.cells tiles) (q.cells tiles)) :
    Disjoint ((relative origin p).cells tiles) ((relative origin q).cells tiles) := by
  rw [Finset.disjoint_left] at h ⊢
  intro c hp hq
  exact h ((mem_relative tiles origin c p).mp hp) ((mem_relative tiles origin c q).mp hq)

end LeanTrominoes.VoxelPlacement
