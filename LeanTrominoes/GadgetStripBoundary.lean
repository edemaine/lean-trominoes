/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripAtlas

/-!
# Blank drawing boundaries close the gadget strip

A locally valid state over a blank drawing cell selects no placement.  Since a
tromino footprint can meet only neighboring lattice blocks, blank first and
last drawing rows prevent every compatible footprint from crossing the finite
vertical strip boundary.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- The two drawing rows adjacent across the vertical period boundary are
blank. -/
def HasBlankVerticalBoundary (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∀ horizontal : Int,
    drawing.getAt (horizontal, -1) = .blank ∧
      drawing.getAt (horizontal, (drawing.verticalPeriod : Int)) = .blank

/-- A verified local tiling of a blank drawing cell contains no placement. -/
theorem localAssignment_eq_empty_of_getAt_eq_blank
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (location : Cell) (blank : drawing.getAt location = .blank) :
    assignment location = ∅ := by
  have localTiling :=
    (mem_exactCellTilings_iff tromino (drawing.getAt location)
      (assignment location)).mp (locallyTiled location)
  rw [blank] at localTiling
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro placement placementMembership
  have admissible := (mem_admissibleCandidates_iff tromino
    (orthogonalCellGadget tromino .blank).window
    (orthogonalCellGadget tromino .blank).region placement).mp
      (localTiling.1 placementMembership)
  obtain ⟨cell, cellInWindow, cellInPlacement⟩ := admissible.1
  have visible : cell ∈ placementWindowCells tromino
      (orthogonalCellGadget tromino .blank).window placement :=
    Finset.mem_inter.mpr ⟨cellInPlacement, cellInWindow⟩
  have impossible := admissible.2 visible
  simp [orthogonalCellGadget, orthogonalCellPixels, paperGadget] at impossible

/-- Consequently, the translated footprint family of a blank drawing block
is empty. -/
theorem drawingBlockFootprints_eq_empty_of_getAt_eq_blank
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (location : Cell) (blank : drawing.getAt location = .blank) :
    drawingBlockFootprints tromino drawing assignment location = ∅ := by
  rw [drawingBlockFootprints,
    localAssignment_eq_empty_of_getAt_eq_blank tromino drawing assignment
      locallyTiled location blank]
  simp [windowFootprints, translateFootprints]

/-- A block neighboring the retained vertical band but lying outside it is
one of the two wraparound boundary rows. -/
theorem outside_neighbor_eq_verticalBoundary
    (drawing : PeriodicOrthogonalDrawing) (first second : Cell)
    (firstRetained : drawing.IsStripBlock first)
    (secondOutside : ¬ drawing.IsStripBlock second)
    (verticalNear : -1 ≤ second.2 - first.2 ∧
      second.2 - first.2 ≤ 1) :
    second.2 = -1 ∨ second.2 = (drawing.verticalPeriod : Int) := by
  unfold IsStripBlock at firstRetained secondOutside
  have periodPositive : 0 < (drawing.verticalPeriod : Int) := by
    simp [verticalPeriod]
  omega

/-- Blank top and bottom drawing rows imply the geometric closure condition
required by the restricted strip atlas. -/
theorem isVerticallyClosed_of_blankVerticalBoundary
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment)
    (blankBoundary : drawing.HasBlankVerticalBoundary) :
    IsVerticallyClosed tromino drawing assignment := by
  let coherent := isGeometricallyCoherent_of_portCompatible tromino drawing
    assignment locallyTiled compatible
  let atlas := footprintAtlasOfAssignment tromino drawing assignment
    locallyTiled coherent
  intro first second footprint firstRetained secondOutside
    footprintMembership meetsSecond
  have footprintShape :=
    (atlas.localTiling first).isFootprint footprint footprintMembership
  have meetsFirst :=
    (atlas.localTiling first).meetsWindow footprint footprintMembership
  have nearby := Tromino.IsFootprint.latticeBlock_bounds
    footprintShape meetsFirst meetsSecond
  have secondBoundary := outside_neighbor_eq_verticalBoundary drawing
    first second firstRetained secondOutside ⟨nearby.2.2.1, nearby.2.2.2⟩
  have secondBlank : drawing.getAt second = .blank := by
    rcases second with ⟨horizontal, vertical⟩
    rcases secondBoundary with lower | upper
    · change vertical = -1 at lower
      subst vertical
      exact (blankBoundary horizontal).1
    · change vertical = (drawing.verticalPeriod : Int) at upper
      subst vertical
      exact (blankBoundary horizontal).2
  have emptyFootprints :=
    drawingBlockFootprints_eq_empty_of_getAt_eq_blank tromino drawing
      assignment locallyTiled second secondBlank
  have secondMembership := coherent first second footprint
    footprintMembership meetsSecond
  rw [emptyFootprints] at secondMembership
  simp at secondMembership

/-- Compatible gadget states on a blank-bordered drawing tile its compiled
strip. -/
theorem periodicStrip_tileable_of_portCompatible_blankBoundary
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment)
    (blankBoundary : drawing.HasBlankVerticalBoundary) :
    tromino.Tileable (drawing.periodicStrip tromino).carrier :=
  periodicStrip_tileable_of_portCompatible_closed tromino drawing assignment
    locallyTiled compatible
    (isVerticallyClosed_of_blankVerticalBoundary tromino drawing assignment
      locallyTiled compatible blankBoundary)

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
