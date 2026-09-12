/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeExtrusion

/-! # Recovering a planar tiling from a horizontal layer -/

namespace LeanTrominoes

namespace VoxelPlacement

def toPlanar {ι : Type*} (p : VoxelPlacement ι) : Placement ι :=
  ⟨p.kind, p.symmetry.planar, p.offset.1⟩

theorem horizontal_cells {ι : Type*} (tiles : ι → Polyomino)
    (p : VoxelPlacement ι) (h : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun i => Polycube.extrude (tiles i) {0}) ↔
      c.1 ∈ p.toPlanar.cells tiles ∧ c.2 = p.offset.2 := by
  simp only [mem_cells_iff, Polycube.mem_extrude, Finset.mem_singleton,
    Placement.mem_cells_iff]
  constructor
  · rintro ⟨⟨source, z⟩, ⟨hs, rfl⟩, he⟩
    simp only [CubeSymmetry.act, h, CubeSymmetry.cycle, Equiv.refl_apply,
      neg_zero, ite_self, Voxel.add, add_zero, Prod.ext_iff] at he
    exact ⟨⟨source, hs, Prod.ext he.1.1 he.1.2⟩, he.2.symm⟩
  · rintro ⟨⟨source, hs, he⟩, hz⟩
    refine ⟨(source, 0), ⟨hs, rfl⟩, ?_⟩
    simpa [CubeSymmetry.act, h, CubeSymmetry.cycle, Voxel.add, toPlanar,
      Prod.ext_iff] using And.intro he hz.symm

end VoxelPlacement

/-- If every tile is a horizontal one-layer extrusion, its zero slice is a
planar tiling. Vertical flips may be freely present among the placements. -/
theorem planar_tileable_of_horizontal_slab {ι : Type*} (tiles : ι → Polyomino)
    {height : Nat} (hh : 0 < height) {placements : Set (VoxelPlacement ι)}
    (tiling : IsVoxelTiling (fun i => Polycube.extrude (tiles i) {0})
      (voxelSlab height) placements)
    (horizontal : ∀ p ∈ placements, p.symmetry.axis = 0) : Tileable tiles Set.univ := by
  let slice : Set (Placement ι) :=
    {q | ∃ p ∈ placements, p.offset.2 = 0 ∧ p.toPlanar = q}
  refine ⟨slice, ⟨?_, ?_⟩⟩
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := tiling.uniqueCover (c, 0) (by
      change 0 ≤ (0 : Int) ∧ (0 : Int) < height
      omega)
    obtain ⟨hplanar, hz⟩ := (p.horizontal_cells tiles (horizontal p hp) (c, 0)).mp hpc
    refine ⟨p.toPlanar, ⟨⟨p, hp, hz.symm, rfl⟩, hplanar⟩, ?_⟩
    rintro q ⟨⟨other, ho, hoz, rfl⟩, hqc⟩
    have hc : (c, 0) ∈ other.cells (fun i => Polycube.extrude (tiles i) {0}) :=
      (other.horizontal_cells tiles (horizontal other ho) (c, 0)).mpr ⟨hqc, hoz.symm⟩
    exact congrArg VoxelPlacement.toPlanar (unique other ⟨ho, hc⟩)

end LeanTrominoes
