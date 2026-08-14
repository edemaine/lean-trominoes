/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMOneDimensionalContractionBand
import LeanTrominoes.PeriodicThreeDMVertexNormalizationStageDrawings
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundOneRoute

/-!
# Vertical-band preservation through the first normalization round
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Starting from band-contained incidence routes of a one-dimensional 3DM
presentation, the complete first normalized drawing remains in its enlarged
open vertical halo. -/
theorem PlanarPresentation.normalizationGridDrawing1_routePointsInExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.drawing.RoutePointsInExpandedVerticalBand) :
    presentation.normalizationGridDrawing1
      |>.RoutePointsInExpandedVerticalBand := by
  have contractedInside :=
    presentation.contractedDrawing_routePointsInExpandedVerticalBand
      horizontal sourceInside
  intro route routeMember point pointMember
  rw [presentation.normalizationGridDrawing1_edgeRoutes] at routeMember
  simp only [PlanarPresentation.normalizationEdgeRoutes1,
    List.mem_map] at routeMember
  rcases routeMember with ⟨tagged, taggedMember, rfl⟩
  have edgeMember : tagged.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have oldRouteMember :
      presentation.contractedEdgeRoute tagged.1 ∈
        presentation.contractedDrawing.edgeRoutes := by
    unfold PlanarPresentation.contractedDrawing
    exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩
  have oldInside :
      presentation.contractedDrawing.PolylineInExpandedVerticalBand
        (presentation.contractedEdgeRoute tagged.1) :=
    fun oldPoint oldPointMember =>
      contractedInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.normalizationRoute1_inExpandedVerticalBand
      horizontal edgeMember oldInside point pointMember
  simpa [PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes
