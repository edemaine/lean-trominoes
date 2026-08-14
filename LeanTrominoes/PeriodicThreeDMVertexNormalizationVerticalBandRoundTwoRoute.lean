/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandCyclicTemplate
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundTwoAnchors
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandSplice

/-!
# Vertical-band preservation for one second-round normalized route
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The first cyclic replacement keeps one round-1 route inside the next
scale-twelve vertical halo. -/
theorem ContinuousPlanarPresentation.normalizationRoute2_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.toPlanarPresentation.normalizationGridDrawing1
        |>.PolylineInExpandedVerticalBand
          (presentation.toPlanarPresentation.normalizationRoute1 edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.toPlanarPresentation.normalizationGridDrawing1)
      |>.PolylineInExpandedVerticalBand
        (presentation.toPlanarPresentation.normalizationRoute2 edge) := by
  let planar := presentation.toPlanarPresentation
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (planar.normalizationRoute1 edge) := by
    have unitSteps := presentation.normalizationRoute1_unitSteps
      wellFormed degree member
    exact unitSteps.imp fun _ _ step => step.isAxisAligned
  have sourceAnchorInside :=
    planar.normalizationPosition1_inExpandedVerticalBand
      endpointMembers.1
  have targetAnchorInside :=
    planar.normalizationTarget1_inExpandedVerticalBand
      horizontal member
  have sourceTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inExpandedVerticalBand
      sourceAnchorInside
      (firstRotationActive planar edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).firstNormalizedPort planar)
  have targetTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inExpandedVerticalBand
      targetAnchorInside
      (firstRotationActive planar edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).firstNormalizedPort planar)
  change
    (vertexNormalizationMagnifiedUnitDrawing
      planar.normalizationGridDrawing1)
      |>.PolylineInExpandedVerticalBand
        (planar.normalizationRoute2 edge)
  unfold PlanarPresentation.normalizationRoute2
  apply normalizeRouteWithTemplates_inExpandedVerticalBand
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.secondNormalizationTemplate,
      ContractedEndpoint.vertex] using sourceTemplateInside
  · simpa [ContractedEndpoint.secondNormalizationTemplate,
      ContractedEndpoint.vertex] using targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes
