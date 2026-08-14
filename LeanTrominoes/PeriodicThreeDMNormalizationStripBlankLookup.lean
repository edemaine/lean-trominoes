/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCellAssignmentBounds

/-!
# Blank lookup on the strip raster's seam rows
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Since every generated assignment has a strict interior row, direct
lookup at row `0` or `3P` returns the blank fallback. -/
theorem ContinuousPlanarPresentation.finalStripCellTypeAt_eq_blank_of_boundary
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (location : Cell)
    (boundary : location.2 = 0 ∨
      location.2 =
        3 * presentation.toPlanarPresentation.finalNormalizationPeriod) :
    presentation.toPlanarPresentation.finalStripCellTypeAt location =
      .blank := by
  let planar := presentation.toPlanarPresentation
  have lookupNone :
      planar.finalStripCellAssignments.lookup location = none := by
    rw [List.lookup_eq_none_iff]
    intro assignment assignmentMember
    have interior :=
      presentation.finalStripCellAssignment_vertical_interior
        wellFormed degree horizontal sourceInside assignmentMember
    rw [bne_iff_ne]
    intro equal
    have verticalEqual := congrArg Prod.snd equal
    rcases boundary with lower | upper
    · rw [lower] at verticalEqual
      omega
    · rw [upper] at verticalEqual
      omega
  unfold PlanarPresentation.finalStripCellTypeAt
  rw [lookupNone]
  rfl

end PeriodicThreeDM
end LeanTrominoes
