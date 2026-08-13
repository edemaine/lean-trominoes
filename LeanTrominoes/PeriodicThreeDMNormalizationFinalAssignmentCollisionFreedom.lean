/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationFinalCyclicRouteSimplicity
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentGeometry

/-!
# Collision freedom of the final normalized raster assignments

The three-round normalization now supplies endpoint-only contacts for the
complete final periodic drawing.  The generic assignment-occurrence theorem
then converts that certificate directly into duplicate-free raster locations.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- The final vertex and route-interior assignments occupy pairwise distinct
locations in the raster torus. -/
theorem ContinuousPlanarPresentation.finalAssignmentsCollisionFree
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.FinalAssignmentsCollisionFree := by
  exact presentation.finalAssignmentsCollisionFree_of_endpointContacts degree
    (presentation.finalNormalizedGridDrawing_routePointsMeetOnlyAtEndpoints
      wellFormed degree separated sourceSimple)

end PeriodicThreeDM
end LeanTrominoes
