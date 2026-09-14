/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-! # The area obstruction for finite tromino regions -/

namespace LeanTrominoes.TrominoFiniteCover

theorem card_dvd_of_tileable (t : Tromino) (cells : List Cell)
    (tiled : t.Tileable (cells.toFinset : Set Cell)) : 3 ∣ cells.toFinset.card := by
  classical
  obtain ⟨footprints,h⟩ := (t.tileable_iff_exists_footprintTiling _).mp tiled
  let selected := cells.toFinset.powerset.filter fun f => f ∈ footprints
  have member : ∀ f, f ∈ selected ↔ f ∈ footprints := by
    intro f
    constructor
    · intro hf
      exact (Finset.mem_filter.mp hf).2
    · intro hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (h.tilesInside f hf).2,hf⟩
  have union : selected.biUnion id = cells.toFinset := by
    ext c
    constructor
    · intro hc
      obtain ⟨f,hf,hfc⟩ := Finset.mem_biUnion.mp hc
      exact (h.tilesInside f ((member f).mp hf)).2 c hfc
    · intro hc
      obtain ⟨f,⟨hf,hfc⟩,_⟩ := h.uniqueCover c hc
      exact Finset.mem_biUnion.mpr ⟨f,(member f).mpr hf,hfc⟩
  have separate : Set.PairwiseDisjoint (selected : Set (Finset Cell)) id := by
    intro f hf g hg neq
    apply Finset.disjoint_left.mpr
    intro c hfc hgc
    exact neq ((h.partial (Set.Subset.refl footprints)).nonoverlap
      f ((member f).mp hf) g ((member g).mp hg) c hfc hgc)
  have cards : ∀ f ∈ selected, (id f).card = 3 := by
    intro f hf
    obtain ⟨p,eq⟩ := (h.tilesInside f ((member f).mp hf)).1
    rw [id_eq,← eq]
    exact t.card_placement_cells p
  rw [← union,Finset.card_biUnion separate]
  simp only [Finset.sum_congr rfl cards,Finset.sum_const,Nat.nsmul_eq_mul]
  exact dvd_mul_left 3 selected.card

end LeanTrominoes.TrominoFiniteCover
