/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoPadding

/-! # A single horizontal row of separated padding rectangles -/

namespace LeanTrominoes.StripTrominoPadding

def region (n : Nat) : Set Cell :=
  {c | (c.1 % n = 14 ∨ c.1 % n = 15) ∧ 4 ≤ c.2 ∧ c.2 ≤ 6}

def placements (n : Nat) : Set (Placement Unit) :=
  {p | p.symmetry = .rotate90 ∧ (p.offset.1 % n = 14 ∨ p.offset.1 % n = 15) ∧ p.offset.2 = 4}

private theorem coordinates (n : Nat) (p : Placement Unit) (hp : p ∈ placements n)
    (c : Cell) (hc : c ∈ p.cells (fun _ => Tromino.I.cells)) :
    c.1 = p.offset.1 ∧ 4 ≤ c.2 ∧ c.2 ≤ 6 := by
  obtain ⟨q,hq,eq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
  simp only [Tromino.cells,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;>
    simp [hp.1,SquareSymmetry.act,Cell.add,hp.2.2,Prod.ext_iff] at eq <;> omega

theorem tileable (n : Nat) : Tromino.I.Tileable (region n) := by
  refine ⟨placements n,?_,?_⟩
  · intro p hp c hc
    obtain ⟨hx,hy⟩ := coordinates n p hp c hc
    exact ⟨hx ▸ hp.2.1,hy⟩
  · intro c hc
    let p : Placement Unit := ⟨(),.rotate90,(c.1,4)⟩
    have hp : p ∈ placements n := ⟨rfl,hc.1,rfl⟩
    have cover : c ∈ p.cells (fun _ => Tromino.I.cells) := by
      apply (Placement.mem_cells_iff _ _ _).mpr
      refine ⟨(c.2-4,0),?_,?_⟩
      · simp [Tromino.cells,Prod.ext_iff]
        have := hc.2
        omega
      · simp [p,Cell.add,SquareSymmetry.act]
    refine ⟨p,⟨hp,cover⟩,?_⟩
    rintro q ⟨hq,hqc⟩
    have coords := coordinates n q hq c hqc
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · exact hq.1
    · exact Prod.ext coords.1.symm hq.2.2

end LeanTrominoes.StripTrominoPadding
