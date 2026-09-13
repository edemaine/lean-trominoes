/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubeTwoBoundary
import LeanTrominoes.BumpyTrominoObstruction
import LeanTrominoes.KeyedPolycubeSpaceSlices

/-! # No upright thickness-two tile can occur in a height-three tiling -/

namespace LeanTrominoes.Polycube

theorem bumpyTwo_horizontal_in_slab {placements : Set (VoxelPlacement Unit)}
    (tiling : IsVoxelTiling (fun _ => bumpyTwo) (voxelSlab 3) placements)
    (p : VoxelPlacement Unit) (hp : p ∈ placements) : p.symmetry.axis = 0 := by
  by_contra upright
  have inside := tiling.tilesInside p hp
  have bounds (q : Voxel) (hq : q ∈ bumpyTwo) :
      0 ≤ p.offset.2 + (p.symmetry.act q).2 ∧ p.offset.2 + (p.symmetry.act q).2 < 3 :=
    inside _ ((p.mem_cells_iff _ _).mpr ⟨q,hq,rfl⟩)
  rcases bumpyTwo_upright_pocket p.symmetry upright with ⟨a,ha,b,hb,span⟩ | pocket
  · have := bounds a ha
    have := bounds b hb
    omega
  · let c := Voxel.add p.offset (p.symmetry.act ((1,1),0))
    have low := bounds ((0,-1),0) (by decide +kernel)
    have high := bounds ((0,1),0) (by decide +kernel)
    have boundary : c.2 = 0 ∨ c.2 = 2 := by dsimp [c,Voxel.add]; omega
    have bar : (c.1,1) ∈ p.cells (fun _ => bumpyTwo) := by
      apply (p.mem_cells_iff _ _).mpr
      refine ⟨((1,0),0),by decide +kernel,?_⟩
      apply Prod.ext
      · simpa [c,Voxel.add] using congrArg (Cell.add p.offset.1) pocket.2.2.1
      · dsimp [Voxel.add]
        omega
    have outside : c ∉ p.cells (fun _ => bumpyTwo) := by
      intro hc
      obtain ⟨q,hq,eq⟩ := (p.mem_cells_iff _ _).mp hc
      have same : q = ((1,1),0) := p.symmetry.act_injective (Voxel.add_left_injective p.offset eq)
      subst q
      exact (by decide +kernel : ((1,1),0) ∉ bumpyTwo) hq
    obtain ⟨q,hq,hqc⟩ := tiling.exists_cover (c := c) (by
      change 0 ≤ c.2 ∧ c.2 < 3
      omega)
    have inward := bumpyTwo_boundary_inward q (tiling.tilesInside q hq) c hqc boundary
    exact Finset.disjoint_left.mp (tiling.disjoint_cells hp hq (by rintro rfl; exact outside hqc)) bar inward

theorem bumpyTwo_horizontal_cells (p : VoxelPlacement Unit)
    (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    c ∈ p.cells (fun _ => bumpyTwo) ↔
      c.1 ∈ p.toPlanar.cells (fun _ => PlusRefinement.bumpy) ∧
      (KeyedPeriodicComplement.sourceHeight p c.2 = 0 ∨
        KeyedPeriodicComplement.sourceHeight p c.2 = 1) := by
  rw [VoxelPlacement.mem_cells_inverse]
  simp only [bumpyTwo,mem_extrude,KeyedPeriodicComplement.cells_source_iff]
  simp [CubeSymmetry.inverseAct,horizontal,CubeSymmetry.cycle,Voxel.sub,
    VoxelPlacement.toPlanar,KeyCornerArithmetic.source,KeyedPeriodicComplement.sourceHeight]

theorem bumpyTwo_not_tileable_slab_three : ¬ VoxelTileableBy bumpyTwo (voxelSlab 3) := by
  rintro ⟨placements,tiling⟩
  apply PlusRefinement.bumpy_not_tileable_plane
  let active : Set (VoxelPlacement Unit) :=
    {p | p ∈ placements ∧ (KeyedPeriodicComplement.sourceHeight p 0 = 0 ∨
      KeyedPeriodicComplement.sourceHeight p 0 = 1)}
  refine ⟨VoxelPlacement.toPlanar '' active,?_,?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨p,⟨hp,hc⟩,unique⟩ := tiling.uniqueCover (c,0) (by
      change 0 ≤ (0 : Int) ∧ (0 : Int) < 3
      omega)
    obtain ⟨planar,height⟩ := (bumpyTwo_horizontal_cells p (bumpyTwo_horizontal_in_slab tiling p hp) (c,0)).mp hc
    refine ⟨p.toPlanar,⟨⟨p,⟨hp,height⟩,rfl⟩,planar⟩,?_⟩
    rintro _ ⟨⟨q,⟨hq,hz⟩,rfl⟩,hqc⟩
    exact congrArg VoxelPlacement.toPlanar (unique q ⟨hq,
      (bumpyTwo_horizontal_cells q (bumpyTwo_horizontal_in_slab tiling q hq) (c,0)).mpr ⟨hqc,hz⟩⟩)

end LeanTrominoes.Polycube
