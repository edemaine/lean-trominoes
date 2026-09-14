/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FootprintTiling
import LeanTrominoes.Gadget

/-! # Exact-cover obstructions for finite tromino regions

Candidates are geometric footprints, eliminating redundant symmetry descriptions.
The finite search is connected to unrestricted tileability, not just a selected
list of sample placements.
-/

namespace LeanTrominoes.TrominoFiniteCover

def candidates (t : Tromino) (cells : List Cell) : List (Finset Cell) :=
  ((cells.flatMap (TrominoAssignment.coveringPlacementList t)).map
    (Placement.cells (fun _ => t.cells))).dedup.filter (fun f => f ⊆ cells.toFinset)

theorem mem_candidates (t : Tromino) (cells : List Cell) (f : Finset Cell) :
    f ∈ candidates t cells ↔ t.IsFootprint f ∧ f ⊆ cells.toFinset := by
  simp only [candidates,List.mem_filter,List.mem_dedup,List.mem_map,List.mem_flatMap,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,_,rfl⟩,inside⟩
    exact ⟨⟨p,rfl⟩,inside⟩
  · rintro ⟨⟨p,rfl⟩,inside⟩
    refine ⟨⟨p,⟨p.offset,List.mem_toFinset.mp (inside (t.offset_mem_placement_cells p)),?_⟩,rfl⟩,inside⟩
    exact (TrominoAssignment.mem_coveringPlacementList_iff t p.offset p).mpr
      ((TrominoAssignment.mem_coveringPlacements_iff t p.offset p).mpr (t.offset_mem_placement_cells p))

def search (t : Tromino) (cells : List Cell) : List (Finset (Finset Cell)) :=
  ExactCover.search Gadget.chooseCell id (candidates t cells) cells.toFinset

theorem search_nonempty_of_tileable (t : Tromino) (cells : List Cell)
    (tiled : t.Tileable (cells.toFinset : Set Cell)) : ∃ selection, selection ∈ search t cells := by
  classical
  obtain ⟨footprints,h⟩ := (t.tileable_iff_exists_footprintTiling _).mp tiled
  let selected := (candidates t cells).toFinset.filter (fun f => f ∈ footprints)
  have selected_iff (f : Finset Cell) : f ∈ selected ↔ f ∈ footprints := by
    constructor
    · intro hf
      exact (Finset.mem_filter.mp hf).2
    · intro hf
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
        ((mem_candidates t cells f).mpr (h.tilesInside f hf)),hf⟩
  refine ⟨selected,(ExactCover.mem_search_iff Gadget.chooseCell Gadget.chooseCell_mem id
    (candidates t cells) cells.toFinset selected).mpr ⟨?_,?_⟩⟩
  · intro f hf
    exact List.mem_toFinset.mp (Finset.mem_filter.mp hf).1
  · rw [ExactCover.isExactCover_iff_card_one]
    constructor
    · intro f hf
      have info := h.tilesInside f ((selected_iff f).mp hf)
      obtain ⟨p,hp⟩ := info.1
      refine ⟨?_,info.2⟩
      rw [← hp]
      exact ⟨p.offset,t.offset_mem_placement_cells p⟩
    · intro c hc
      obtain ⟨f,⟨hf,hfc⟩,unique⟩ := h.uniqueCover c hc
      apply Finset.card_eq_one.mpr
      refine ⟨f,Finset.ext fun g => ?_⟩
      simp only [Finset.mem_filter,Finset.mem_singleton,id_eq]
      constructor
      · rintro ⟨hg,hgc⟩
        exact unique g ⟨(selected_iff g).mp hg,hgc⟩
      · rintro rfl
        exact ⟨(selected_iff _).mpr hf,hfc⟩

theorem not_tileable_of_search_empty (t : Tromino) (cells : List Cell)
    (empty : search t cells = []) : ¬ t.Tileable (cells.toFinset : Set Cell) := by
  intro tiled
  obtain ⟨selection,member⟩ := search_nonempty_of_tileable t cells tiled
  simp [empty] at member

end LeanTrominoes.TrominoFiniteCover
