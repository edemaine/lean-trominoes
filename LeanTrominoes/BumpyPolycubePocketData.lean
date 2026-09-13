/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeExtrusion
import LeanTrominoes.PolycubeCovering
import Mathlib.Tactic.IntervalCases

/-! # Finite data for the thickness-three pocket certificates -/
namespace LeanTrominoes.Polycube.BumpyPocket

abbrev family : Unit → Polycube := fun _ => bumpyThree

def candidates (s : CubeSymmetry) (c : Voxel) : Finset (VoxelPlacement Unit) :=
  (VoxelPlacement.coveringPlacements bumpyThree (s.act c)).filter fun p =>
    Disjoint ((VoxelPlacement.reference s).cells family) (p.cells family)

def contains (c : Voxel) : Prop :=
  0 ≤ c.2 ∧ c.2 ≤ 2 ∧
    ((c.1.2 = 0 ∧ -1 ≤ c.1.1 ∧ c.1.1 ≤ 7) ∨
      ((c.1.2 = 1 ∨ c.1.2 = -1) ∧ (c.1.1 = 0 ∨ c.1.1 = 3 ∨ c.1.1 = 6)))

instance (c : Voxel) : Decidable (contains c) := by unfold contains; infer_instance

private theorem bumpy_explicit : PlusRefinement.bumpy =
    {(-1, 0), (0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0),
     (0, 1), (0, -1), (3, 1), (3, -1), (6, 1), (6, -1)} := by decide +kernel

theorem contains_iff (c : Voxel) : contains c ↔ c ∈ bumpyThree := by
  rcases c with ⟨⟨x, y⟩, z⟩
  have planar :
      ((y = 0 ∧ -1 ≤ x ∧ x ≤ 7) ∨
        ((y = 1 ∨ y = -1) ∧ (x = 0 ∨ x = 3 ∨ x = 6))) ↔
        (x, y) ∈ PlusRefinement.bumpy := by
    rw [bumpy_explicit]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, hx, hx'⟩ | ⟨hy, hx⟩)
      · interval_cases x <;> decide
      · rcases hy with rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> decide
    · intro h
      omega
  have layers : (0 ≤ z ∧ z ≤ 2) ↔ z ∈ ({0, 1, 2} : Finset Int) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  constructor
  · rintro ⟨hz₀, hz₂, hxy⟩
    exact (mem_extrude _ _ _).mpr ⟨planar.mp hxy, layers.mp ⟨hz₀, hz₂⟩⟩
  · intro h
    obtain ⟨hxy, hz⟩ := (mem_extrude _ _ _).mp h
    exact ⟨(layers.mpr hz).1, (layers.mpr hz).2, planar.mpr hxy⟩

def covers (p : VoxelPlacement Unit) (c : Voxel) : Prop :=
  contains (p.symmetry.inverseAct (Voxel.sub c p.offset))

instance (p : VoxelPlacement Unit) (c : Voxel) : Decidable (covers p c) := by
  unfold covers; infer_instance

theorem covers_iff (p : VoxelPlacement Unit) (c : Voxel) :
    covers p c ↔ c ∈ p.cells family := by
  rw [VoxelPlacement.mem_cells_inverse]
  exact contains_iff _

def compatible (s : CubeSymmetry) (p : VoxelPlacement Unit) : Prop :=
  ∀ c ∈ bumpyThree, ¬ covers p (s.act c)

instance (s : CubeSymmetry) (p : VoxelPlacement Unit) : Decidable (compatible s p) := by
  unfold compatible; infer_instance

theorem compatible_of_disjoint (s : CubeSymmetry) (p : VoxelPlacement Unit)
    (h : Disjoint ((VoxelPlacement.reference s).cells family) (p.cells family)) :
    compatible s p := by
  intro c hc hp
  have href : s.act c ∈ (VoxelPlacement.reference s).cells family := by
    apply (VoxelPlacement.mem_cells_iff _ _ _).mpr
    exact ⟨c, hc, by simp [VoxelPlacement.reference, Voxel.add, Cell.add]⟩
  exact (Finset.disjoint_left.mp h) href ((covers_iff _ _).mp hp)

def FirstCertificate (s : CubeSymmetry) : Prop :=
  ∀ t : CubeSymmetry, ∀ c ∈ bumpyThree,
    let p := VoxelPlacement.covering (s.act ((1, 1), 1)) t c
    compatible s p → covers p (s.act ((1, 2), 1)) ∧ ¬ covers p (s.act ((2, 1), 1))

def SecondCertificate (s : CubeSymmetry) : Prop :=
  ∀ t : CubeSymmetry, ∀ c ∈ bumpyThree,
    let p := VoxelPlacement.covering (s.act ((2, 1), 1)) t c
    compatible s p → covers p (s.act ((1, 2), 1))

instance (s : CubeSymmetry) : Decidable (FirstCertificate s) := by
  unfold FirstCertificate
  infer_instance
instance (s : CubeSymmetry) : Decidable (SecondCertificate s) := by
  unfold SecondCertificate
  infer_instance

end LeanTrominoes.Polycube.BumpyPocket
