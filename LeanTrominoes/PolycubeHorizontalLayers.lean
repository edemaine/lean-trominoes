/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeLayerAssembly

/-! # Horizontal slices with arbitrary vertical offsets and reflections -/

namespace LeanTrominoes.VoxelPlacement

theorem toVoxel_toPlanar {ι : Type*} (p : VoxelPlacement ι)
    (horizontal : p.symmetry.axis = 0) (unflipped : p.symmetry.flip = false)
    (height : p.offset.2 = 0) : p.toPlanar.toVoxel = p := by
  rcases p with ⟨k, ⟨s, f, a⟩, ⟨o, z⟩⟩
  dsimp at horizontal unflipped height
  subst a
  subst f
  subst z
  rfl

theorem horizontal_layer_cells {ι : Type*} (tiles : ι → Polyomino)
    (z : Int) (p : VoxelPlacement ι) (h : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun i => Polycube.extrude (tiles i) {z}) ↔
      c.1 ∈ p.toPlanar.cells tiles ∧
        c.2 = p.offset.2 + (if p.symmetry.flip then -z else z) := by
  simp only [mem_cells_iff, Polycube.mem_extrude, Finset.mem_singleton,
    Placement.mem_cells_iff]
  constructor
  · rintro ⟨⟨source, height⟩, ⟨hs, rfl⟩, he⟩
    simp only [CubeSymmetry.act, h, CubeSymmetry.cycle, Equiv.refl_apply,
      Voxel.add, Prod.ext_iff] at he
    exact ⟨⟨source, hs, Prod.ext he.1.1 he.1.2⟩, he.2.symm⟩
  · rintro ⟨⟨source, hs, he⟩, hz⟩
    refine ⟨(source, z), ⟨hs, rfl⟩, ?_⟩
    simpa [CubeSymmetry.act, h, CubeSymmetry.cycle, Voxel.add, toPlanar,
      Prod.ext_iff] using And.intro he hz.symm

theorem horizontal_capped_cells {ι : Type*} (bottom top : ι → Polyomino)
    (p : VoxelPlacement ι) (h : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun i => Polycube.capped (bottom i) (top i) {0} 1) ↔
      (c.1 ∈ p.toPlanar.cells bottom ∧ c.2 = p.offset.2) ∨
        (c.1 ∈ p.toPlanar.cells top ∧
          c.2 = p.offset.2 + (if p.symmetry.flip then -1 else 1)) := by
  have distribute :
      p.cells (fun i => Polycube.capped (bottom i) (top i) {0} 1) =
        p.cells (fun i => Polycube.extrude (bottom i) {0}) ∪
          p.cells (fun i => Polycube.extrude (top i) {1}) := by
    simp [cells, Polycube.capped, Finset.image_union]
  rw [distribute, Finset.mem_union, horizontal_layer_cells bottom 0 p h,
    horizontal_layer_cells top 1 p h]
  simp

end LeanTrominoes.VoxelPlacement
