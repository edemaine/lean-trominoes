/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripRouteBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripVertexBounds

/-!
# Vertical bounds for all strip-raster assignments
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every prioritized vertex or route assignment occupies a strict interior
row of the rectangular strip raster. -/
theorem ContinuousPlanarPresentation.finalStripCellAssignment_vertical_interior
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
      presentation.toPlanarPresentation.finalStripCellAssignments) :
    0 < assignment.1.2 ∧
      assignment.1.2 <
        3 * presentation.toPlanarPresentation.finalNormalizationPeriod := by
  simp only [PlanarPresentation.finalStripCellAssignments,
    List.mem_append] at member
  rcases member with vertexMember | routeMember
  · exact presentation.toPlanarPresentation
      |>.finalStripVertexAssignment_vertical_interior vertexMember
  · exact presentation.finalStripRouteAssignment_vertical_interior
      wellFormed degree horizontal sourceInside routeMember

end PeriodicThreeDM
end LeanTrominoes
