/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoSeparatedUnion

/-! # A separated periodic 2-by-3 padding rectangle -/

namespace LeanTrominoes.PeriodicTrominoPadding

/-- A 2-by-3 rectangle at `(14,4)` in each square period. -/
def region (n : Nat) : Set Cell :=
  {c | (c.1 % n = 14 ∨ c.1 % n = 15) ∧ 4 ≤ c.2 % n ∧ c.2 % n ≤ 6}

def placements (n : Nat) : Set (Placement Unit) :=
  {p | p.symmetry = .rotate90 ∧
    (p.offset.1 % n = 14 ∨ p.offset.1 % n = 15) ∧ p.offset.2 % n = 4}

private def covering (n : Nat) (c : Cell) : Placement Unit :=
  ⟨(), .rotate90, (c.1, c.2 - c.2 % n + 4)⟩

private theorem small_mod {n : Nat} (hn : 72 ≤ n) {k : Int} (hk : 0 ≤ k ∧ k ≤ 15) :
    k % (n : Int) = k := Int.emod_eq_of_lt hk.1 (by omega)

theorem mem_of_coordinates {n : Nat} (hn : 72 ≤ n) (c : Cell)
    (hx : c.1 = 14 ∨ c.1 = 15) (hy : 4 ≤ c.2 ∧ c.2 ≤ 6) : c ∈ region n := by
  have cx : c.1 % (n : Int) = c.1 := small_mod hn (by omega)
  have cy : c.2 % (n : Int) = c.2 := small_mod hn (by omega)
  change (c.1 % n = 14 ∨ c.1 % n = 15) ∧ 4 ≤ c.2 % n ∧ c.2 % n ≤ 6
  rw [cx, cy]
  exact ⟨hx, hy⟩

/-- Padding remains in the reserved source gap when the period is a multiple
of the gadget residue period. -/
theorem residues_mod_seventyTwo {n : Nat} (divisor : (72 : Int) ∣ (n : Int))
    (c : Cell) (hc : c ∈ region n) :
    (c.1 % 72 = 14 ∨ c.1 % 72 = 15) ∧ 4 ≤ c.2 % 72 ∧ c.2 % 72 ≤ 6 := by
  have ex := Int.emod_emod_of_dvd c.1 divisor
  have ey := Int.emod_emod_of_dvd c.2 divisor
  have small : (c.2 % (n : Int)) % 72 = c.2 % n :=
    Int.emod_eq_of_lt (by have := hc.2.1; omega) (by have := hc.2.2; omega)
  rw [ey] at small
  refine ⟨?_, ?_⟩
  · rcases hc.1 with hx | hx
    · left
      rw [← ex, hx]
      rfl
    · right
      rw [← ex, hx]
      rfl
  · rw [small]
    exact hc.2

private theorem source_bounds {q : Cell} (hq : q ∈ Tromino.I.cells) :
    q.2 = 0 ∧ 0 ≤ q.1 ∧ q.1 ≤ 2 := by
  simp only [Tromino.cells, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl <;> decide

private theorem source_mem (r : Int) (lower : 4 ≤ r) (upper : r ≤ 6) :
    (r - 4, 0) ∈ Tromino.I.cells := by
  simp only [Tromino.cells, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, and_true]
  omega

private theorem cell_coordinates {n : Nat} (hn : 72 ≤ n) (p : Placement Unit)
    (hp : p ∈ placements n) (c : Cell) (hc : c ∈ p.cells (fun _ => Tromino.I.cells)) :
    c.1 = p.offset.1 ∧ ∃ i : Int, 0 ≤ i ∧ i ≤ 2 ∧ c.2 = p.offset.2 + i ∧ c.2 % n = 4 + i := by
  obtain ⟨q, hq, eq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
  obtain ⟨qy, qi₀, qi₁⟩ := source_bounds hq
  have ex := congrArg Prod.fst eq
  have ey := congrArg Prod.snd eq
  simp only [hp.1, SquareSymmetry.act, Cell.add, qy, Int.neg_zero, Int.add_zero] at ex ey
  refine ⟨ex.symm, q.1, qi₀, qi₁, ey.symm, ?_⟩
  rw [← ey, Int.add_emod, hp.2.2, small_mod hn ⟨qi₀, by omega⟩]
  exact small_mod hn (by omega)

/-- Two vertical I trominoes tile every padding rectangle. -/
theorem tileable {n : Nat} (hn : 72 ≤ n) : Tromino.I.Tileable (region n) := by
  refine ⟨placements n, ?_, ?_⟩
  · intro p hp c hc
    obtain ⟨ex, i, hi₀, hi₁, _, residue⟩ := cell_coordinates hn p hp c hc
    change (c.1 % n = 14 ∨ c.1 % n = 15) ∧ 4 ≤ c.2 % n ∧ c.2 % n ≤ 6
    exact ⟨ex ▸ hp.2.1, by omega, by omega⟩
  · intro c hc
    change (c.1 % (n : Int) = 14 ∨ c.1 % (n : Int) = 15) ∧
      4 ≤ c.2 % (n : Int) ∧ c.2 % (n : Int) ≤ 6 at hc
    have member : covering n c ∈ placements n := by
      refine ⟨rfl, hc.1, ?_⟩
      dsimp [covering]
      simp only [Int.add_emod, Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod,
        Int.zero_add, small_mod hn (k := 4) (by omega)]
    have covers : c ∈ (covering n c).cells (fun _ => Tromino.I.cells) := by
      apply (Placement.mem_cells_iff _ _ _).mpr
      refine ⟨(c.2 % n - 4, 0), ?_, ?_⟩
      · exact source_mem _ hc.2.1 hc.2.2
      · apply Prod.ext <;> dsimp [covering, Cell.add, SquareSymmetry.act] <;> omega
    refine ⟨covering n c, ⟨member, covers⟩, ?_⟩
    rintro p ⟨hp, hpc⟩
    obtain ⟨ex, i, hi₀, hi₁, ey, residue⟩ := cell_coordinates hn p hp c hpc
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · exact hp.1
    · apply Prod.ext <;> dsimp [covering] <;> omega

end LeanTrominoes.PeriodicTrominoPadding
