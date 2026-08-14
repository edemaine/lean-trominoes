/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentBounds
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandFinal

/-!
# Vertical bounds for strip-raster route assignments
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every final normalized route assignment occupies a strict interior row
of the rectangular strip raster. -/
theorem ContinuousPlanarPresentation.finalStripRouteAssignment_vertical_interior
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈
      presentation.toPlanarPresentation.finalStripRouteAssignments) :
    0 < assignment.1.2 ∧
      assignment.1.2 <
        3 * presentation.toPlanarPresentation.finalNormalizationPeriod := by
  let planar := presentation.toPlanarPresentation
  simp only [PlanarPresentation.finalStripRouteAssignments,
    List.mem_flatMap] at member
  rcases member with ⟨edge, edgeMember, assignmentMember⟩
  have drawingInside :=
    presentation.finalNormalizedGridDrawing_routePointsInExpandedVerticalBand
      wellFormed degree horizontal sourceInside
  have routeMember :
      planar.finalNormalizationRoute edge ∈
        planar.finalNormalizedGridDrawing.edgeRoutes := by
    rw [planar.finalNormalizedGridDrawing_edgeRoutes_eq_map]
    exact List.mem_map.mpr ⟨edge, edgeMember, rfl⟩
  have routeInside :
      planar.finalNormalizedGridDrawing.PolylineInExpandedVerticalBand
        (planar.finalNormalizationRoute edge) :=
    fun point pointMember =>
      drawingInside _ routeMember _ pointMember
  have assignmentMember' :
      assignment ∈
        stripRouteInteriorAssignments
          planar.finalNormalizedGridDrawing.gridSize edge.color
          (planar.finalNormalizationRoute edge) := by
    rwa [planar.finalNormalizedGridDrawing_gridSize]
  have interior :=
    stripRouteInteriorAssignment_vertical_interior
      routeInside assignmentMember'
  rwa [planar.finalNormalizedGridDrawing_gridSize] at interior

end PeriodicThreeDM
end LeanTrominoes
