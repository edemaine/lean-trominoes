/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeConnected

/-! # A capped background placement in the height-two slab

Its cap forces it to be horizontal. Its vertical offset is then determined
by its vertical reflection: 0 for an upward cap and 1 for a downward cap.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

private theorem upright_cap_span :
    ∀ s : CubeSymmetry, s.axis ≠ 0 →
      ∃ a ∈ square 3, ∃ b ∈ square 3,
        (s.act (a, 1)).2 + 2 ≤ (s.act (b, 1)).2 := by decide +kernel

theorem slabTile_horizontal {n : Nat} (hn : 3 ≤ n) (holes : Polyomino)
    (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => slabTile n holes), c ∈ voxelSlab 2) :
    p.symmetry.axis = 0 := by
  by_contra hn'
  obtain ⟨a, ha, b, hb, span⟩ := upright_cap_span p.symmetry hn'
  have cap_inside (c : Cell) (hc : c ∈ square 3) : (c, 1) ∈ slabTile n holes := by
    have h := (mem_square 3 c).mp hc
    have hs : c ∈ square n := (mem_square n c).mpr (by omega)
    simp [slabTile, hs]
  have ha' := inside (Voxel.add p.offset (p.symmetry.act (a, 1)))
    ((p.mem_cells_iff _ _).mpr ⟨(a, 1), cap_inside a ha, rfl⟩)
  have hb' := inside (Voxel.add p.offset (p.symmetry.act (b, 1)))
    ((p.mem_cells_iff _ _).mpr ⟨(b, 1), cap_inside b hb, rfl⟩)
  simp only [voxelSlab, Set.mem_setOf_eq, Voxel.add] at ha' hb'
  omega

theorem slabTile_vertical_offset {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : VoxelPlacement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => slabTile n holes), c ∈ voxelSlab 2) :
    p.offset.2 = if p.symmetry.flip then 1 else 0 := by
  have horizontal := slabTile_horizontal (by omega : 3 ≤ n) holes p inside
  have bottom : ((0, 0), 0) ∈ slabTile n holes := by
    have hq : (0, 0) ∈ tile n holes := lower_tile hn holes admissible (by
      simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
        KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock]
      omega)
    simp [slabTile, hq]
  have top : ((0, 0), 1) ∈ slabTile n holes := by
    simp [slabTile, mem_square]
    omega
  have hbottom := inside (Voxel.add p.offset (p.symmetry.act ((0, 0), 0)))
    ((p.mem_cells_iff _ _).mpr ⟨((0, 0), 0), bottom, rfl⟩)
  have htop := inside (Voxel.add p.offset (p.symmetry.act ((0, 0), 1)))
    ((p.mem_cells_iff _ _).mpr ⟨((0, 0), 1), top, rfl⟩)
  simp only [voxelSlab, Set.mem_setOf_eq, Voxel.add, CubeSymmetry.act,
    horizontal, CubeSymmetry.cycle, Equiv.refl_apply] at hbottom htop
  cases hf : p.symmetry.flip <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte, neg_zero] at * <;>
    dsimp at hbottom htop <;> omega

end LeanTrominoes.KeyedPeriodicComplement
