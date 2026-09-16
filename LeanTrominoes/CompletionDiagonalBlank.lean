/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalEquivalence

/-! # Removing the refinement scaffold over blank source cells -/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

theorem blank_iff (v : Fin 4 → Bool) : Network 0 v ↔ ∀ p, v p = false := by
  revert v
  decide +kernel

theorem allFalse_wire (r : Fin 8) : Network (wireLabel r) (fun _ => false) := by
  fin_cases r <;> decide +kernel

def boundedPalette (palette : Cell → Fin 24) (c : Cell) : Fin 24 :=
  if palette (sourceAt c) = 0 then 0 else refinePalette palette c

@[simp] theorem boundedPalette_place (palette : Cell → Fin 24) (c : Cell) (r : Fin 8) :
    boundedPalette palette (place c r) =
      if palette c = 0 then 0 else if r = 0 then palette c else wireLabel r := by
  simp [boundedPalette]

theorem bounded_implies_refined (palette : Cell → Fin 24) (v : Cell → Fin 4 → Bool)
    (h : SquareNetwork (boundedPalette palette) v) : SquareNetwork (refinePalette palette) v := by
  refine ⟨h.1,?_⟩
  intro c
  by_cases blank : palette (sourceAt c) = 0
  · have allFalse := (blank_iff _).mp (by simpa [boundedPalette,blank] using h.2 c)
    have eq : v c = fun _ => false := funext allFalse
    rw [eq]
    unfold refinePalette
    rw [blank]
    split
    · exact (blank_iff _).mpr (by simp)
    · exact allFalse_wire _
  · simpa [boundedPalette,blank] using h.2 c

theorem bounded_lift (palette : Cell → Fin 24) (v : Cell → Fin 4 → Bool)
    (h : SquareNetwork palette v) : SquareNetwork (boundedPalette palette) (liftValue v) := by
  refine ⟨lift_seams v h.1,?_⟩
  intro c
  by_cases blank : palette (sourceAt c) = 0
  · have allFalse : ∀ p, v (sourceAt c) p = false := (blank_iff _).mp (by simpa [blank] using h.2 (sourceAt c))
    simp only [boundedPalette,if_pos blank]
    apply (blank_iff _).mpr
    intro p
    simp [liftValue,liftAt,allFalse]
  · simpa [boundedPalette,blank] using (lift_network palette v h).2 c

theorem bounded_holds_iff (palette : Cell → Fin 24) :
    SquareHolds (boundedPalette palette) ↔ SquareHolds palette := by
  constructor
  · rintro ⟨v,hv⟩
    exact (refine_holds_iff palette).mp ⟨v,bounded_implies_refined palette v hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨liftValue v,bounded_lift palette v hv⟩

/-- A finite-height source remains finite-height in brick coordinates. -/
theorem bounded_support (palette : Cell → Fin 24) (lower upper : Int)
    (outside : ∀ c, c.2 < lower ∨ upper < c.2 → palette c = 0) (b : Cell)
    (hb : b.2 < 4*lower-1 ∨ 4*upper+3 < b.2) :
    boundedPalette palette (squareOfBrick b) = 0 := by
  let c := sourceAt (squareOfBrick b)
  let r := roleAt (squareOfBrick b)
  have eq : brickOfSquare (place c r) = b := by simp [c,r,place_source_role]
  have bounds := brick_row_bounds c r
  rw [eq] at bounds
  have blank : palette c = 0 := outside c (by omega)
  change palette (sourceAt (squareOfBrick b)) = 0 at blank
  simp [boundedPalette,blank]

end LeanTrominoes.CompletionPattern.DiagonalRouting
