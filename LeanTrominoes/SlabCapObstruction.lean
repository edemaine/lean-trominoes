/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementVerticalNeighbor

/-! # A square cap cannot cover either simulation-layer lock

Each lock has occupied neighbors immediately to its left and right. A
square of side at least two covering the lock must cover one of them.
-/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem square_covers_neighbor {n : Nat} (hn : 2 ≤ n) (p : Placement Unit) (c : Cell)
    (hc : c ∈ p.cells (fun _ => square n)) :
    Cell.add c (-1, 0) ∈ p.cells (fun _ => square n) ∨
      Cell.add c (1, 0) ∈ p.cells (fun _ => square n) := by
  simp only [cells_source_iff, mem_square] at hc ⊢
  cases hs : p.symmetry <;> simp only [hs] at hc ⊢ <;>
    dsimp [KeyCornerArithmetic.source, SquareSymmetry.inverse, SquareSymmetry.act,
      Cell.add, Cell.sub] at hc ⊢ <;> omega

theorem square_cannot_cover_between {n : Nat} (hn : 2 ≤ n) (obstacle : Polyomino)
    (p : Placement Unit) (c : Cell)
    (left : Cell.add c (-1, 0) ∈ obstacle) (right : Cell.add c (1, 0) ∈ obstacle)
    (hc : c ∈ p.cells (fun _ => square n)) :
    ¬ Disjoint obstacle (p.cells (fun _ => square n)) := by
  intro hd
  rcases square_covers_neighbor hn p c hc with hl | hr
  · exact (Finset.disjoint_left.mp hd) left hl
  · exact (Finset.disjoint_left.mp hd) right hr

theorem square_cannot_fill_vertical_lock {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : Placement Unit)
    (covers : (2, 3) ∈ p.cells (fun _ => square n)) :
    ¬ Disjoint (tile n holes) (p.cells (fun _ => square n)) := by
  apply square_cannot_cover_between (by omega : 2 ≤ n) (tile n holes) p (2, 3) ?_ ?_ covers
  all_goals
    apply lower_tile hn holes admissible
    simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
      KeyCornerArithmetic.inKey, Cell.add]
    omega

theorem square_cannot_fill_right_lock {n : Nat} (hn : 96 ≤ n) (holes : Polyomino)
    (admissible : AdmissibleHoles n holes) (p : Placement Unit)
    (covers : ((n : Int) - 4, 2) ∈ p.cells (fun _ => square n)) :
    ¬ Disjoint (tile n holes) (p.cells (fun _ => square n)) := by
  apply square_cannot_cover_between (by omega : 2 ≤ n) (tile n holes) p ((n : Int) - 4, 2)
    ?_ ?_ covers
  all_goals
    apply lower_tile hn holes admissible
    simp [KeyCornerArithmetic.lower, KeyCornerArithmetic.inBox,
      KeyCornerArithmetic.inVerticalLock, KeyCornerArithmetic.inHorizontalLock,
      KeyCornerArithmetic.inKey, Cell.add]
    omega

end LeanTrominoes.KeyedPeriodicComplement
