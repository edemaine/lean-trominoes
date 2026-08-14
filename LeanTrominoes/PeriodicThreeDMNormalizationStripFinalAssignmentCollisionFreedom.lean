/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationFinalAssignmentCollisionFreedom

/-!
# Collision freedom of the final normalized strip assignments

The established three-round endpoint-contact theorem supplies the geometric
hypothesis needed by the rectangular strip rasterizer.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- The final vertex and route-interior assignments occupy pairwise distinct
locations in the rectangular strip raster. -/
theorem ContinuousPlanarPresentation.finalStripAssignmentsCollisionFree
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree := by
  exact presentation.toPlanarPresentation
    |>.finalStripAssignmentsCollisionFree_of_finalAssignmentsCollisionFree
      (presentation.finalAssignmentsCollisionFree
        wellFormed degree separated sourceSimple)

end PeriodicThreeDM
end LeanTrominoes
