/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoFiniteCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The area obstruction for finite tromino regions -/

namespace LeanTrominoes.TrominoFiniteCover

theorem card_dvd_of_tileable (t : Tromino) (cells : List Cell)
    (tiled : t.Tileable (cells.toFinset : Set Cell)) : 3 ∣ cells.toFinset.card := by
  obtain ⟨selected,hs⟩ := search_nonempty_of_tileable t cells tiled
  obtain ⟨admissible,cover⟩ := (ExactCover.mem_search_iff Gadget.chooseCell Gadget.chooseCell_mem
    id (candidates t cells) cells.toFinset selected).mp hs
  have cards : ∀ f ∈ selected, (id f).card = 3 := by
    intro f hf
    obtain ⟨p,eq⟩ := ((mem_candidates t cells f).mp (admissible f hf)).1
    rw [id_eq,← eq]
    exact t.card_placement_cells p
  rw [← cover.union_eq,Finset.card_biUnion cover.pairwiseDisjoint]
  simp only [Finset.sum_congr rfl cards,Finset.sum_const,nsmul_eq_mul]
  exact dvd_mul_left 3 selected.card

end LeanTrominoes.TrominoFiniteCover
