/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinementGeometry

/-! # Exact equivalence between I-tromino tilings and refined 15-omino tilings -/

namespace LeanTrominoes.PlusRefinement

/-- Divide the translation of an aligned placement by three. -/
def contractPlacement (p : Placement Unit) : Placement Unit :=
  {p with offset := (p.offset.1 / 3, p.offset.2 / 3)}

theorem expand_contract (p : Placement Unit)
    (aligned : p.offset.1 % 3 = 0 ∧ p.offset.2 % 3 = 0) :
    expandPlacement (contractPlacement p) = p := by
  apply Placement.ext
  · rfl
  · rfl
  · simp only [expandPlacement, contractPlacement, Cell.scale]
    apply Prod.ext <;> dsimp <;> omega

/-- A tiling of the refined region contracts to an I-tromino tiling. -/
theorem bumpy_tileable_contract (original : Set Cell)
    (h : TileableBy bumpy (region original)) : Tromino.I.Tileable original := by
  classical
  obtain ⟨placements, ht⟩ := h
  let coarse : Set (Placement Unit) := {p | expandPlacement p ∈ placements}
  have covers_center (p : Placement Unit) (parent : Cell)
      (hc : parent ∈ p.cells (fun _ => Tromino.I.cells)) :
      pixel parent (0, 0) ∈ (expandPlacement p).cells (fun _ => bumpy) :=
    (mem_expanded_cells _ _ _).mpr ⟨parent, hc, _, by decide, rfl⟩
  refine ⟨coarse, ?_, ?_⟩
  · intro p hp parent hc
    have inside := ht.tilesInside (expandPlacement p) hp _ (covers_center p parent hc)
    obtain ⟨other, ho, subcell, hu, he⟩ := inside
    obtain ⟨rfl, -⟩ := pixel_injective hu (show (0, 0) ∈ cross by decide) he
    exact ho
  · intro parent hp
    have refined : pixel parent (0, 0) ∈ region original :=
      ⟨parent, hp, _, by decide, rfl⟩
    obtain ⟨p, ⟨hpmem, hpc⟩, unique⟩ := ht.uniqueCover _ refined
    have aligned := bumpy_placement_aligned p original (ht.tilesInside p hpmem)
    have ep := expand_contract p aligned
    have hcoarse : contractPlacement p ∈ coarse := by
      change expandPlacement (contractPlacement p) ∈ placements
      rwa [ep]
    have hcell : parent ∈ (contractPlacement p).cells (fun _ => Tromino.I.cells) := by
      rw [← ep] at hpc
      obtain ⟨other, ho, subcell, hu, he⟩ := (mem_expanded_cells _ _ _).mp hpc
      obtain ⟨rfl, -⟩ := pixel_injective hu (show (0, 0) ∈ cross by decide) he
      exact ho
    refine ⟨contractPlacement p, ⟨hcoarse, hcell⟩, ?_⟩
    rintro other ⟨ho, hc⟩
    apply expandPlacement_injective
    rw [ep]
    exact unique (expandPlacement other) ⟨ho, covers_center other parent hc⟩

/-- The refinement is exact for every region, without periodicity assumptions. -/
theorem bumpy_tileable_refinement_iff (original : Set Cell) :
    TileableBy bumpy (region original) ↔ Tromino.I.Tileable original := by
  constructor
  · exact bumpy_tileable_contract original
  · exact tileable_refinement (fun _ : Unit => Tromino.I.cells) original

end LeanTrominoes.PlusRefinement
