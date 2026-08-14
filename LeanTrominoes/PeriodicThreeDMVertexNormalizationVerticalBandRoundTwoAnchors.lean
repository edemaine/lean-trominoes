/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationStageDrawings
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandPosition
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundOneAnchors

/-!
# Vertical-band bounds for second-round normalization anchors
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained vertex anchor after round 1 lies in the first normalized
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition1_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.normalizationGridDrawing1.PositionInExpandedVerticalBand
      (presentation.normalizationPosition1 vertex) := by
  have inside := normalizeVertexPosition_inExpandedVerticalBand
    (presentation.normalizationPosition0_inExpandedVerticalBand member)
  simpa [PlanarPresentation.normalizationPosition1,
    PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

/-- The target anchor after round 1 is the affine image of the old horizontal
target occurrence and lies in the first normalized drawing's halo. -/
theorem PlanarPresentation.normalizationTarget1_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.normalizationGridDrawing1.PositionInExpandedVerticalBand
      (presentation.normalizationTarget1 edge) := by
  have inside := normalizeVertexPosition_inExpandedVerticalBand
    (presentation.normalizationTarget0_inExpandedVerticalBand
      horizontal member)
  simpa [PlanarPresentation.normalizationTarget1,
    PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes
