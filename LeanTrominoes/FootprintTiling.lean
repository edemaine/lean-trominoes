/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling

/-!
# Geometric tromino-footprint tilings

A geometric copy of a tromino can have several representation-level
descriptions as a `Placement`: symmetries that stabilize the prototile may
produce the same three occupied cells.  Gadget ports therefore record finite
cell footprints rather than placements.  This file proves that no tiling
information is lost by that choice.
-/

namespace LeanTrominoes
namespace Tromino

/-- A finite cell set is the geometric footprint of a placed copy of the
specified tromino. -/
def IsFootprint (tromino : Tromino) (footprint : Finset Cell) : Prop :=
  ∃ placement : Placement Unit,
    placement.cells (fun _ : Unit => tromino.cells) = footprint

/-- An exact tiling expressed using geometric footprints instead of
representation-level placements. -/
structure IsFootprintTiling (tromino : Tromino) (region : Set Cell)
    (footprints : Set (Finset Cell)) : Prop where
  tilesInside :
    ∀ footprint ∈ footprints,
      tromino.IsFootprint footprint ∧ ∀ cell ∈ footprint, cell ∈ region
  uniqueCover :
    ∀ cell ∈ region,
      ∃! footprint : Finset Cell, footprint ∈ footprints ∧ cell ∈ footprint

/-- Tromino tileability is unchanged when selected placements are quotiented
by equality of their occupied cell footprints. -/
theorem tileable_iff_exists_footprintTiling (tromino : Tromino)
    (region : Set Cell) :
    tromino.Tileable region ↔
      ∃ footprints : Set (Finset Cell),
        IsFootprintTiling tromino region footprints := by
  constructor
  · rintro ⟨placements, tiling⟩
    let footprints : Set (Finset Cell) :=
      { footprint | ∃ placement ∈ placements,
          placement.cells (fun _ : Unit => tromino.cells) = footprint }
    refine ⟨footprints, ?_⟩
    constructor
    · intro footprint footprintMember
      obtain ⟨placement, placementMember, rfl⟩ := footprintMember
      exact ⟨⟨placement, rfl⟩,
        fun cell cellMember =>
          tiling.tilesInside placement placementMember cell cellMember⟩
    · intro cell cellMember
      obtain ⟨placement, ⟨placementMember, placementCovers⟩, unique⟩ :=
        tiling.uniqueCover cell cellMember
      refine ⟨placement.cells (fun _ : Unit => tromino.cells),
        ⟨⟨placement, placementMember, rfl⟩, placementCovers⟩, ?_⟩
      intro otherFootprint otherCovers
      obtain ⟨otherPlacement, otherPlacementMember, otherEquality⟩ :=
        otherCovers.1
      have otherPlacementCovers :
          cell ∈ otherPlacement.cells (fun _ : Unit => tromino.cells) := by
        rw [otherEquality]
        exact otherCovers.2
      have placementEquality := unique otherPlacement
        ⟨otherPlacementMember, otherPlacementCovers⟩
      simpa only [placementEquality] using otherEquality.symm
  · rintro ⟨footprints, tiling⟩
    classical
    let representative :
        ∀ footprint : Finset Cell, footprint ∈ footprints → Placement Unit :=
      fun footprint footprintMember =>
        Classical.choose (tiling.tilesInside footprint footprintMember).1
    have representativeCells (footprint : Finset Cell)
        (footprintMember : footprint ∈ footprints) :
        (representative footprint footprintMember).cells
            (fun _ : Unit => tromino.cells) = footprint :=
      Classical.choose_spec (tiling.tilesInside footprint footprintMember).1
    let placements : Set (Placement Unit) :=
      { placement | ∃ (footprint : Finset Cell)
          (footprintMember : footprint ∈ footprints),
          representative footprint footprintMember = placement }
    refine ⟨placements, ?_⟩
    constructor
    · intro placement placementMember cell cellMember
      obtain ⟨footprint, footprintMember, representativeEquality⟩ :=
        placementMember
      have footprintCell : cell ∈ footprint := by
        rw [← representativeCells footprint footprintMember,
          representativeEquality]
        exact cellMember
      exact (tiling.tilesInside footprint footprintMember).2 cell footprintCell
    · intro cell cellMember
      obtain ⟨footprint, ⟨footprintMember, footprintCovers⟩, unique⟩ :=
        tiling.uniqueCover cell cellMember
      let placement := representative footprint footprintMember
      refine ⟨placement, ⟨⟨footprint, footprintMember, rfl⟩, ?_⟩, ?_⟩
      · rw [representativeCells footprint footprintMember]
        exact footprintCovers
      · intro otherPlacement otherCovers
        obtain ⟨otherFootprint, otherFootprintMember,
          otherRepresentativeEquality⟩ := otherCovers.1
        have otherFootprintCovers : cell ∈ otherFootprint := by
          rw [← representativeCells otherFootprint otherFootprintMember,
            otherRepresentativeEquality]
          exact otherCovers.2
        have footprintEquality := unique otherFootprint
          ⟨otherFootprintMember, otherFootprintCovers⟩
        subst otherFootprint
        exact otherRepresentativeEquality.symm

end Tromino
end LeanTrominoes
