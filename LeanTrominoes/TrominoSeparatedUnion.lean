/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingUnion
import LeanTrominoes.PolyominoConnectivity

/-! # Adding separated I-tromino-tileable padding -/

namespace LeanTrominoes

/-- An I tromino cannot cross between regions having no side-adjacent cells. -/
theorem i_placement_separated (s t : Set Cell)
    (separated : ∀ a ∈ s, ∀ b ∈ t, ¬ Cell.SideAdjacent a b)
    (p : Placement Unit)
    (inside : ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ s ∪ t) :
    (∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ s) ∨
      (∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ t) := by
  let v (i : Int) := Cell.add p.offset (p.symmetry.act (i, 0))
  have cases_cell {c : Cell} (hc : c ∈ p.cells (fun _ => Tromino.I.cells)) :
      c = v 0 ∨ c = v 1 ∨ c = v 2 := by
    obtain ⟨q, hq, eq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
    simp only [Tromino.cells, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl eq.symm
    · exact Or.inr (Or.inl eq.symm)
    · exact Or.inr (Or.inr eq.symm)
  have h0 : v 0 ∈ s ∪ t := inside _ ((Placement.mem_cells_iff _ _ _).mpr
    ⟨(0, 0), by decide, rfl⟩)
  have h1 : v 1 ∈ s ∪ t := inside _ ((Placement.mem_cells_iff _ _ _).mpr
    ⟨(1, 0), by decide, rfl⟩)
  have h2 : v 2 ∈ s ∪ t := inside _ ((Placement.mem_cells_iff _ _ _).mpr
    ⟨(2, 0), by decide, rfl⟩)
  have step (i : Int) : Cell.SideAdjacent (v i) (v (i + 1)) := by
    cases hs : p.symmetry <;> simp [v, hs, SquareSymmetry.act, Cell.add, Cell.SideAdjacent] <;> omega
  have extend_s {a b : Cell} (ha : a ∈ s) (hb : b ∈ s ∪ t) (adj : Cell.SideAdjacent a b) :
      b ∈ s := hb.resolve_right (fun ht => separated a ha b ht adj)
  have extend_t {a b : Cell} (ha : a ∈ t) (hb : b ∈ s ∪ t) (adj : Cell.SideAdjacent a b) :
      b ∈ t := by
    apply hb.resolve_left
    intro hs
    apply separated b hs a ha
    unfold Cell.SideAdjacent at adj ⊢
    omega
  by_cases hs0 : v 0 ∈ s
  · have hs1 := extend_s hs0 h1 (step 0)
    have hs2 := extend_s hs1 h2 (step 1)
    left
    intro c hc
    rcases cases_cell hc with rfl | rfl | rfl <;> assumption
  · have ht0 := h0.resolve_left hs0
    have ht1 := extend_t ht0 h1 (step 0)
    have ht2 := extend_t ht1 h2 (step 1)
    right
    intro c hc
    rcases cases_cell hc with rfl | rfl | rfl <;> assumption

/-- A separately tileable padding region with a blank gap preserves exactly
the original I-tromino tileability question. -/
theorem i_tileable_union_iff (s t : Set Cell) (disjoint : Disjoint s t)
    (separated : ∀ a ∈ s, ∀ b ∈ t, ¬ Cell.SideAdjacent a b)
    (padding : Tromino.I.Tileable t) :
    Tromino.I.Tileable (s ∪ t) ↔ Tromino.I.Tileable s := by
  constructor
  · exact Tileable.restrict_left _ s t disjoint (i_placement_separated s t separated)
  · intro h
    exact Tileable.union _ s t disjoint h padding

end LeanTrominoes
