/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripBoundary
import LeanTrominoes.PeriodicOrthogonalDrawingBoundaryResidues
import LeanTrominoes.PeriodicThreeDMNormalizationStripBlankLookup
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback

/-!
# Blank vertical boundaries of the normalized 3DM strip raster
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The two rows adjacent across the rectangular drawing's artificial
vertical period are exactly its unassigned seam rows and therefore blank. -/
theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_hasBlankVerticalBoundary
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
      |>.HasBlankVerticalBoundary := by
  let planar := presentation.toPlanarPresentation
  intro horizontalCoordinate
  constructor
  · unfold Gadget.PeriodicOrthogonalDrawing.getAt
    rw [planar.stripNormalizedOrthogonalDrawing_get]
    apply presentation.finalStripCellTypeAt_eq_blank_of_boundary
      wellFormed degree horizontal sourceInside
    right
    change
      ((Gadget.PeriodicOrthogonalDrawing.residue
        (-1) (3 * planar.finalNormalizationPeriod)).val : Int) =
        3 * planar.finalNormalizationPeriod
    exact Gadget.PeriodicOrthogonalDrawing.residue_neg_one_val_int _
  · unfold Gadget.PeriodicOrthogonalDrawing.getAt
    rw [planar.stripNormalizedOrthogonalDrawing_get]
    apply presentation.finalStripCellTypeAt_eq_blank_of_boundary
      wellFormed degree horizontal sourceInside
    left
    change
      ((Gadget.PeriodicOrthogonalDrawing.residue
        ((3 * planar.finalNormalizationPeriod + 1 : Nat) : Int)
        (3 * planar.finalNormalizationPeriod)).val : Int) = 0
    have castPeriod :
        ((3 * planar.finalNormalizationPeriod + 1 : Nat) : Int) =
          (3 * planar.finalNormalizationPeriod : Nat) + 1 := by
      norm_num
    rw [castPeriod]
    exact Gadget.PeriodicOrthogonalDrawing.residue_period_val_int _

end PeriodicThreeDM
end LeanTrominoes
