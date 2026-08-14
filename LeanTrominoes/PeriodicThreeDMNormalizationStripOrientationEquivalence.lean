/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardOrientationValidity
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseElementConstraints

/-!
# Orientation equivalence for normalized periodic 3DM strip drawings
-/

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Strip drawing orientation is equivalent to the suppressed incidence
orientation represented by its contracted routes. -/
theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_hasOrientation_iff_hasSuppressedOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    (presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing).HasOrientation ↔
      problem.HasSuppressedOrientation := by
  constructor
  · rintro ⟨drawingWellFormed, orientation, valid⟩
    have collisionFree := presentation.finalStripAssignmentsCollisionFree
      wellFormed degree separated sourceSimple
    exact ⟨presentation.toPlanarPresentation.reverseStripGraphOrientation
        orientation,
      presentation.reverseStripGraphOrientation_isSuppressedOrientation
        wellFormed degree horizontal sourceInside collisionFree orientation
          valid⟩
  · rintro ⟨values, valid⟩
    exact presentation.stripNormalizedOrthogonalDrawing_hasOrientation
      wellFormed degree horizontal sourceInside separated sourceSimple values
        valid

/-- The normalized strip drawing is orientable exactly when the original
periodic 3DM instance has a perfect matching. -/
theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    (presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing).HasOrientation ↔
      problem.Satisfiable := by
  rw [presentation.stripNormalizedOrthogonalDrawing_hasOrientation_iff_hasSuppressedOrientation
    wellFormed degree horizontal sourceInside separated sourceSimple]
  exact (problem.satisfiable_iff_hasSuppressedOrientation degree).symm

end PeriodicThreeDM

end LeanTrominoes
