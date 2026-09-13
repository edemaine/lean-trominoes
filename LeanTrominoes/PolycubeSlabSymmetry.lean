/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTranslation
import LeanTrominoes.TilingSymmetry

/-! # Coordinate changes for horizontal slab tilings -/

namespace LeanTrominoes

theorem IsVoxelTiling.pullback {ι : Type*} {tiles : ι → Polycube} {region : Set Voxel}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles region placements)
    (world : Voxel ≃ Voxel) (records : VoxelPlacement ι ≃ VoxelPlacement ι)
    (invariant : ∀ c, world c ∈ region ↔ c ∈ region)
    (geometry : ∀ p, records p ∈ placements → ∀ c,
      world c ∈ (records p).cells tiles ↔ c ∈ p.cells tiles) :
    IsVoxelTiling tiles region {p | records p ∈ placements} := by
  constructor
  · intro p hp c hc
    exact (invariant c).mp (tiling.tilesInside _ hp _ ((geometry p hp c).mpr hc))
  · intro c hc
    obtain ⟨a, ⟨ha, covers⟩, unique⟩ := tiling.uniqueCover (world c) ((invariant c).mpr hc)
    let p := records.symm a
    have hp : records p ∈ placements := by simpa [p] using ha
    have hpc : c ∈ p.cells tiles := (geometry p hp c).mp (by simpa [p] using covers)
    refine ⟨p, ⟨hp, hpc⟩, ?_⟩
    intro b hb
    apply records.injective
    change records b = records (records.symm a)
    rw [records.apply_symm_apply]
    exact unique (records b) ⟨hb.1, (geometry b hb.1 c).mpr hb.2⟩

namespace VoxelPlacement

def orient {ι : Type*} (s : SquareSymmetry) (p : VoxelPlacement ι) : VoxelPlacement ι :=
  ⟨p.kind, ⟨s.compose p.symmetry.planar, p.symmetry.flip, p.symmetry.axis⟩,
    (s.act p.offset.1, p.offset.2)⟩

@[simp] theorem orient_cancel {ι : Type*} (s : SquareSymmetry) (p : VoxelPlacement ι) :
    (p.orient s.inverse).orient s = p := by
  rcases p with ⟨k, ⟨t, f, a⟩, ⟨o, z⟩⟩
  simp [orient, SquareSymmetry.compose_inverse_cancel]

def orientEquiv {ι : Type*} (s : SquareSymmetry) : VoxelPlacement ι ≃ VoxelPlacement ι where
  toFun := orient s
  invFun := orient s.inverse
  left_inv p := by
    have hi : s.inverse.inverse = s := by cases s <;> rfl
    simpa only [hi] using orient_cancel s.inverse p
  right_inv := orient_cancel s

theorem mem_orient_cells {ι : Type*} (tiles : ι → Polycube) (s : SquareSymmetry)
    (p : VoxelPlacement ι) (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    (s.act c.1, c.2) ∈ (p.orient s).cells tiles ↔ c ∈ p.cells tiles := by
  rcases c with ⟨xy, z⟩
  simp only [mem_cells_iff, orient, CubeSymmetry.act, horizontal, CubeSymmetry.cycle,
    Equiv.refl_apply, Voxel.add, SquareSymmetry.act_compose, ← SquareSymmetry.act_add,
    Prod.mk.injEq, SquareSymmetry.act_injective s |>.eq_iff]

def reflectSlab {ι : Type*} (p : VoxelPlacement ι) : VoxelPlacement ι :=
  ⟨p.kind, ⟨p.symmetry.planar, !p.symmetry.flip, p.symmetry.axis⟩,
    (p.offset.1, 1 - p.offset.2)⟩

@[simp] theorem reflectSlab_involutive {ι : Type*} (p : VoxelPlacement ι) :
    p.reflectSlab.reflectSlab = p := by
  rcases p with ⟨k, ⟨s, f, a⟩, ⟨o, z⟩⟩
  simp [reflectSlab]

def reflectSlabEquiv {ι : Type*} : VoxelPlacement ι ≃ VoxelPlacement ι where
  toFun := reflectSlab
  invFun := reflectSlab
  left_inv := reflectSlab_involutive
  right_inv := reflectSlab_involutive

theorem mem_reflectSlab_cells {ι : Type*} (tiles : ι → Polycube)
    (p : VoxelPlacement ι) (horizontal : p.symmetry.axis = 0) (c : Voxel) :
    (c.1, 1 - c.2) ∈ p.reflectSlab.cells tiles ↔ c ∈ p.cells tiles := by
  rcases c with ⟨xy, z⟩
  simp only [mem_cells_iff, reflectSlab, CubeSymmetry.act, horizontal, CubeSymmetry.cycle,
    Equiv.refl_apply, Voxel.add, Prod.mk.injEq]
  cases p.symmetry.flip <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> rintro ⟨q, hq, hxy, hz⟩ <;>
    exact ⟨q, hq, hxy, by omega⟩

end VoxelPlacement

theorem IsVoxelTiling.reorient_slab {ι : Type*} {tiles : ι → Polycube} {height : Nat}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles (voxelSlab height) placements)
    (horizontal : ∀ p ∈ placements, p.symmetry.axis = 0) (s : SquareSymmetry) :
    IsVoxelTiling tiles (voxelSlab height) {p | p.orient s ∈ placements} := by
  apply tiling.pullback (s.cellEquiv.prodCongr (Equiv.refl Int)) (VoxelPlacement.orientEquiv s)
  · intro c
    rfl
  · intro p hp c
    exact p.mem_orient_cells tiles s (horizontal ((VoxelPlacement.orientEquiv s) p) hp) c

def slabReflection : Voxel ≃ Voxel where
  toFun c := (c.1, 1 - c.2)
  invFun c := (c.1, 1 - c.2)
  left_inv c := by simp
  right_inv c := by simp

theorem IsVoxelTiling.reflect_slab {ι : Type*} {tiles : ι → Polycube}
    {placements : Set (VoxelPlacement ι)} (tiling : IsVoxelTiling tiles (voxelSlab 2) placements)
    (horizontal : ∀ p ∈ placements, p.symmetry.axis = 0) :
    IsVoxelTiling tiles (voxelSlab 2) {p | p.reflectSlab ∈ placements} := by
  apply tiling.pullback slabReflection VoxelPlacement.reflectSlabEquiv
  · intro c
    change (0 ≤ 1 - c.2 ∧ 1 - c.2 < (2 : Int)) ↔ 0 ≤ c.2 ∧ c.2 < (2 : Int)
    omega
  · intro p hp c
    exact p.mem_reflectSlab_cells tiles (horizontal (VoxelPlacement.reflectSlabEquiv p) hp) c

end LeanTrominoes
