/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalBlank
import LeanTrominoes.CompletionISquareNetwork

/-! # Horizontal periods and geometric correctness of diagonal refinement -/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

def brickPalette (palette : Cell → Fin 24) (b : Cell) : Fin 24 :=
  boundedPalette palette (squareOfBrick b)

theorem brickPalette_period (palette : Cell → Fin 24) (p : Int)
    (periodic : ∀ c, palette (c.1+p,c.2) = palette c) (b : Cell) :
    brickPalette palette (Cell.add b (2*p,0)) = brickPalette palette b := by
  let c := sourceAt (squareOfBrick b)
  let r := roleAt (squareOfBrick b)
  have eq : brickOfSquare (place c r) = b := by simp [c,r,place_source_role]
  rw [← eq,← brick_horizontal_period]
  simp only [brickPalette,square_of_brick_of_square,boundedPalette_place,periodic]

theorem brickPalette_support (palette : Cell → Fin 24) (lower upper : Int)
    (outside : ∀ c, c.2 < lower ∨ upper < c.2 → palette c = 0) (b : Cell)
    (hb : b.2 < 4*lower-1 ∨ 4*upper+3 < b.2) : brickPalette palette b = 0 :=
  bounded_support palette lower upper outside b hb

theorem lCompletion_iff (palette : Cell → Fin 24) :
    Tromino.L.Completable Set.univ (LBricks.globalPrescribed (brickPalette palette)) ↔
      LBricks.SquareHolds palette := by
  change Tromino.L.Completable Set.univ (LBricks.globalPrescribed
    (fun c => boundedPalette palette (squareOfBrick c))) ↔ _
  rw [← LBricks.square_holds_iff_completion,bounded_holds_iff]

theorem iCompletion_iff (palette : Cell → Fin 24) :
    Tromino.I.Completable Set.univ (IBricks.globalPrescribed (brickPalette palette)) ↔
      LBricks.SquareHolds palette := by
  change Tromino.I.Completable Set.univ (IBricks.globalPrescribed
    (fun c => boundedPalette palette (IBricks.squareOfBrick c))) ↔ _
  rw [← IBricks.square_holds_iff_completion]
  exact bounded_holds_iff palette

/-- The physical horizontal period of the L-brick prefill. -/
theorem l_origin_period (b : Cell) (p : Int) :
    LBricks.origin (Cell.add b (2*p,0)) = Cell.add (LBricks.origin b) (48*p,0) := by
  apply Prod.ext <;> simp [LBricks.origin,Cell.add] <;> ring

/-- The physical horizontal period of the I-brick prefill. -/
theorem i_origin_period (b : Cell) (p : Int) :
    IBricks.origin (Cell.add b (2*p,0)) = Cell.add (IBricks.origin b) (72*p,0) := by
  apply Prod.ext <;> simp [IBricks.origin,Cell.add] <;> ring

end LeanTrominoes.CompletionPattern.DiagonalRouting
