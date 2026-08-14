/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentBounds
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing

/-!
# Vertical bounds for strip-raster vertex assignments
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every final normalized vertex assignment occupies a strict interior row
of the rectangular strip raster. -/
theorem PlanarPresentation.finalStripVertexAssignment_vertical_interior
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalStripVertexAssignments) :
    0 < assignment.1.2 ∧
      assignment.1.2 < 3 * presentation.finalNormalizationPeriod := by
  simp only [PlanarPresentation.finalStripVertexAssignments,
    List.mem_map] at member
  rcases member with ⟨vertex, vertexMember, rfl⟩
  have positionMember :
      presentation.finalNormalizationPosition vertex ∈
        presentation.finalNormalizedVertexPositions := by
    rw [presentation.finalNormalizedVertexPositions_eq_map]
    exact List.mem_map.mpr ⟨vertex, vertexMember, rfl⟩
  have fundamental :=
    presentation.finalNormalizedPositions_in_fundamental_square
      _ positionMember
  have inside :=
    PeriodicGridDrawing.positionInExpandedVerticalBand_of_fundamentalSquare
      fundamental
  have interior := stripRasterLocation_vertical_interior inside
  rwa [presentation.finalNormalizedGridDrawing_gridSize] at interior

end PeriodicThreeDM
end LeanTrominoes
