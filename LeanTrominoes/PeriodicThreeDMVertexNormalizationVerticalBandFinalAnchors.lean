/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundTwoAnchors

/-!
# Vertical-band bounds for final-round normalization anchors
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained vertex anchor after round 2 lies in the second normalized
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition2_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.normalizationGridDrawing2.PositionInExpandedVerticalBand
      (presentation.normalizationPosition2 vertex) := by
  have inside := normalizeVertexPosition_inExpandedVerticalBand
    (presentation.normalizationPosition1_inExpandedVerticalBand member)
  simpa [PlanarPresentation.normalizationPosition2,
    PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

/-- The target anchor after round 2 is the affine image of the previous
horizontal target occurrence and lies in the second normalized halo. -/
theorem PlanarPresentation.normalizationTarget2_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.normalizationGridDrawing2.PositionInExpandedVerticalBand
      (presentation.normalizationTarget2 edge) := by
  have inside := normalizeVertexPosition_inExpandedVerticalBand
    (presentation.normalizationTarget1_inExpandedVerticalBand
      horizontal member)
  simpa [PlanarPresentation.normalizationTarget2,
    PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes
