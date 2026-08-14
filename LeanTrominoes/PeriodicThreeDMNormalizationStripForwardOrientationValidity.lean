/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationStripWellFormed

/-!
# Validity of the forward normalized strip orientation
-/

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- The forward construction is a valid global orientation of the compiled
normalized strip drawing. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_isOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
      |>.IsOrientation (presentation.forwardStripDrawingOrientation values) := by
  unfold PeriodicOrthogonalDrawing.IsOrientation
  constructor
  · intro location
    let planar := presentation.toPlanarPresentation
    generalize lookup : planar.finalStripOrientationSiteAt location = found
    cases found with
    | none =>
        have blank :=
          planar.stripNormalizedOrthogonalDrawing_getAt_eq_blank_of_site_none
            lookup
        rw [blank]
        simp [PeriodicOrthogonalDrawing.satisfiesOrientation]
    | some site =>
        have cellType :=
          planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
            collisionFree lookup
        rw [cellType]
        have orientationEq :
            presentation.forwardStripDrawingOrientation values location =
              site.inward planar values
                (planar.finalStripOrientationSiteOccurrenceTranslate
                  location site) := by
          funext side
          unfold ContinuousPlanarPresentation.forwardStripDrawingOrientation
          dsimp only
          rw [lookup]
        rw [orientationEq]
        have stripMember := List.mem_of_lookup_eq_some lookup
        rcases planar.exists_finalOrientationSite_of_mem_finalStripOrientationSites
            stripMember with ⟨squareLocation, squareMember⟩
        exact presentation.finalOrientationSite_satisfiesOrientation
          wellFormed degree values valid squareMember
            (planar.finalStripOrientationSiteOccurrenceTranslate location site)
  · intro location side exposed
    have neighborConstraint :=
      @ContinuousPlanarPresentation.forwardStripDrawingOrientation_neighbor
        problem presentation wellFormed degree horizontal sourceInside
          collisionFree values valid location side exposed
    exact neighborConstraint

/-- Any suppressed orientation induces an orientation of the normalized
periodic strip drawing. -/
theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_hasOrientation
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
        LocalIncidenceDrawing.RouteIsSimple route)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
      |>.HasOrientation := by
  have collisionFree := presentation.finalStripAssignmentsCollisionFree
    wellFormed degree separated sourceSimple
  exact ⟨presentation.stripNormalizedOrthogonalDrawing_isWellFormed
      wellFormed degree horizontal sourceInside separated sourceSimple,
    presentation.forwardStripDrawingOrientation values,
    presentation.forwardStripDrawingOrientation_isOrientation
      wellFormed degree horizontal sourceInside collisionFree values valid⟩

end PeriodicThreeDM

end LeanTrominoes
