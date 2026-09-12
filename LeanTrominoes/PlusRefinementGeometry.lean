/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement

/-! # Rigid placements and cross refinement -/

namespace LeanTrominoes.PlusRefinement

theorem cross_symmetry : ∀ s : SquareSymmetry, ∀ c ∈ cross, s.act c ∈ cross := by
  decide

theorem pixel_motion (s : SquareSymmetry) (offset parent subcell : Cell) :
    Cell.add (Cell.scale 3 offset) (s.act (pixel parent subcell)) =
      pixel (Cell.add offset (s.act parent)) (s.act subcell) := by
  cases s <;> apply Prod.ext <;>
    simp [pixel, Cell.add, Cell.scale, SquareSymmetry.act, Int.mul_add] <;> omega

/-- Refining a placement scales its translation by three. -/
def expandPlacement {ι : Type*} (p : Placement ι) : Placement ι :=
  {p with offset := Cell.scale 3 p.offset}

theorem expandPlacement_injective {ι : Type*} :
    Function.Injective (@expandPlacement ι) := by
  intro p q h
  apply Placement.ext
  · simpa only [expandPlacement] using congrArg Placement.kind h
  · simpa only [expandPlacement] using congrArg Placement.symmetry h
  · have ho := congrArg Placement.offset h
    simp only [expandPlacement, Cell.scale, Prod.mk.injEq] at ho
    apply Prod.ext <;> omega

/-- Refinement commutes with every allowed rigid placement. -/
theorem mem_expanded_cells {ι : Type*} (tiles : ι → Polyomino) (p : Placement ι)
    (c : Cell) :
    c ∈ (expandPlacement p).cells (fun i => polyomino (tiles i)) ↔
      ∃ parent ∈ p.cells tiles, ∃ subcell ∈ cross, pixel parent subcell = c := by
  constructor
  · intro hc
    obtain ⟨source, hs, he⟩ := (Placement.mem_cells_iff _ _ _).mp hc
    obtain ⟨parent, hp, subcell, hu, rfl⟩ := (mem_polyomino _ _).mp hs
    refine ⟨Cell.add p.offset (p.symmetry.act parent),
      (Placement.mem_cells_iff _ _ _).mpr ⟨parent, hp, rfl⟩,
      p.symmetry.act subcell, cross_symmetry _ _ hu, ?_⟩
    exact (pixel_motion _ _ _ _).symm.trans he
  · rintro ⟨parent, hp, subcell, hu, rfl⟩
    obtain ⟨source, hs, rfl⟩ := (Placement.mem_cells_iff _ _ _).mp hp
    apply (Placement.mem_cells_iff _ _ _).mpr
    refine ⟨pixel source (p.symmetry.inverse.act subcell),
      (mem_polyomino _ _).mpr ⟨source, hs, _, cross_symmetry _ _ hu, rfl⟩, ?_⟩
    change Cell.add (Cell.scale 3 p.offset)
      (p.symmetry.act (pixel source (p.symmetry.inverse.act subcell))) = _
    rw [pixel_motion, SquareSymmetry.act_inverse_act]

/-- A tiling lifts to the cross-refined region. -/
theorem tileable_refinement {ι : Type*} (tiles : ι → Polyomino) (original : Set Cell)
    (h : Tileable tiles original) :
    Tileable (fun i => polyomino (tiles i)) (region original) := by
  classical
  obtain ⟨placements, ht⟩ := h
  refine ⟨expandPlacement '' placements, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ c hc
    obtain ⟨parent, hparent, subcell, hu, rfl⟩ := (mem_expanded_cells _ _ _).mp hc
    exact ⟨parent, ht.tilesInside p hp parent hparent, subcell, hu, rfl⟩
  · rintro c ⟨parent, hparent, subcell, hu, rfl⟩
    obtain ⟨p, ⟨hp, hpc⟩, unique⟩ := ht.uniqueCover parent hparent
    refine ⟨expandPlacement p, ⟨⟨p, hp, rfl⟩,
      (mem_expanded_cells _ _ _).mpr ⟨parent, hpc, subcell, hu, rfl⟩⟩, ?_⟩
    rintro q ⟨⟨other, ho, rfl⟩, hc⟩
    obtain ⟨otherParent, hop, otherSubcell, hou, he⟩ :=
      (mem_expanded_cells _ _ _).mp hc
    obtain ⟨rfl, rfl⟩ := pixel_injective hou hu he
    exact congrArg expandPlacement (unique other ⟨ho, hop⟩)

/-- Every refined pixel lies on a horizontal or vertical line of the 3-grid. -/
theorem region_mod_three {original : Set Cell} {c : Cell} (hc : c ∈ region original) :
    c.1 % 3 = 0 ∨ c.2 % 3 = 0 := by
  obtain ⟨parent, -, subcell, hu, rfl⟩ := hc
  simp only [cross, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    simp [pixel, Cell.add, Cell.scale]

theorem cross_subset_bumpy : cross ⊆ bumpy := by decide

/-- Every orientation of the bumpy tile contains the cross at its offset. -/
theorem offset_cross_mem (p : Placement Unit) {u : Cell} (hu : u ∈ cross) :
    Cell.add p.offset u ∈ p.cells (fun _ => bumpy) := by
  apply (Placement.mem_cells_iff _ _ _).mpr
  refine ⟨p.symmetry.inverse.act u, cross_subset_bumpy (cross_symmetry _ _ hu), ?_⟩
  rw [SquareSymmetry.act_inverse_act]

/-- Containment in a refined region forces placement on the coarse lattice. -/
theorem bumpy_placement_aligned (p : Placement Unit) (original : Set Cell)
    (inside : ∀ c ∈ p.cells (fun _ => bumpy), c ∈ region original) :
    p.offset.1 % 3 = 0 ∧ p.offset.2 % 3 = 0 := by
  have h₀ := region_mod_three (inside _ (offset_cross_mem p (show (0, 0) ∈ cross by decide)))
  have hx := region_mod_three (inside _ (offset_cross_mem p (show (1, 0) ∈ cross by decide)))
  have hy := region_mod_three (inside _ (offset_cross_mem p (show (0, 1) ∈ cross by decide)))
  simp only [Cell.add, add_zero] at h₀ hx hy
  omega

end LeanTrominoes.PlusRefinement
