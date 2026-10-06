/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.GadgetCore
import LeanTrominoes.ExactCoverImage

/-! # Gadget search without duplicate geometric tile representations -/

namespace LeanTrominoes.Gadget

def geometricCandidateList (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : List (Finset Cell) :=
  ((admissibleCandidateList tromino gadget.window regionCells).map
    (Placement.cells (fun _ : Unit => tromino.cells))).dedup

def geometricWindowTilings (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : List (Finset (Finset Cell)) :=
  ExactCover.search chooseCell (fun tile => tile ∩ gadget.window)
    (geometricCandidateList tromino gadget regionCells) gadget.region

theorem mem_geometricWindowTilings_iff (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region)
    (selection : Finset (Finset Cell)) :
    selection ∈ geometricWindowTilings tromino gadget regionCells ↔
      ∃ placements, IsWindowTiling tromino gadget.window gadget.region placements ∧
        placements.image (Placement.cells (fun _ : Unit => tromino.cells)) =
          selection := by
  have candidateMember (tile : Finset Cell) :
      tile ∈ geometricCandidateList tromino gadget regionCells ↔
        tile ∈ (admissibleCandidates tromino gadget.window gadget.region).image
          (Placement.cells (fun _ : Unit => tromino.cells)) := by
    simp only [geometricCandidateList, List.mem_dedup, List.mem_map,
      Finset.mem_image]
    apply exists_congr
    intro placement
    rw [mem_admissibleCandidateList_iff tromino gadget wellFormed
      regionCells regionEquality placement]
  rw [geometricWindowTilings,
    ExactCover.mem_search_iff chooseCell chooseCell_mem]
  simp_rw [candidateMember]
  change selection ⊆ _ ∧ _ ↔ _
  rw [ExactCover.exists_cover_image_iff]
  constructor
  · rintro ⟨placements, subset, cover, imageEq⟩
    exact ⟨placements,
      (isWindowTiling_iff_exactCover tromino gadget.window gadget.region
        wellFormed placements).mpr ⟨subset, cover⟩, imageEq⟩
  · rintro ⟨placements, tiled, imageEq⟩
    have data := (isWindowTiling_iff_exactCover tromino gadget.window
      gadget.region wellFormed placements).mp tiled
    exact ⟨placements, data.1, data.2, imageEq⟩

theorem boundarySignature_eq_filter_image (tromino : Tromino)
    (window : Finset Cell) (placements : Finset (Placement Unit)) :
    boundarySignature tromino window placements =
      (placements.image (Placement.cells (fun _ : Unit => tromino.cells))).filter
        (fun tile => ¬ tile ⊆ window) := by
  ext tile
  simp only [boundarySignature, boundaryPlacements,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨placement, ⟨member, crossing⟩, rfl⟩
    exact ⟨⟨placement, member, rfl⟩, crossing⟩
  · rintro ⟨⟨placement, member, rfl⟩, crossing⟩
    exact ⟨placement, ⟨member, crossing⟩, rfl⟩

def geometricBoundarySignatures (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : Finset (Finset (Finset Cell)) :=
  ((geometricWindowTilings tromino gadget regionCells).map
    (fun selection => selection.filter (fun tile => ¬ tile ⊆ gadget.window))).toFinset

theorem geometricBoundarySignatures_eq (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region) :
    geometricBoundarySignatures tromino gadget regionCells =
      boundarySignatures tromino gadget.window gadget.region := by
  ext boundary
  rw [mem_boundarySignatures_iff]
  simp only [geometricBoundarySignatures, List.mem_toFinset, List.mem_map,
    mem_geometricWindowTilings_iff tromino gadget wellFormed regionCells regionEquality]
  constructor
  · rintro ⟨selection, ⟨placements, tiled, imageEq⟩, boundaryEq⟩
    refine ⟨placements, tiled, ?_⟩
    rw [boundarySignature_eq_filter_image, imageEq]
    exact boundaryEq
  · rintro ⟨placements, tiled, boundaryEq⟩
    refine ⟨placements.image (Placement.cells (fun _ : Unit => tromino.cells)),
      ⟨placements, tiled, rfl⟩, ?_⟩
    rw [← boundarySignature_eq_filter_image]
    exact boundaryEq

end LeanTrominoes.Gadget
