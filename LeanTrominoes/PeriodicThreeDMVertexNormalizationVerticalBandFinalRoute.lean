/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandCyclicTemplate
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandFinalAnchors
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandSplice

/-!
# Vertical-band preservation for one final normalized route
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The second cyclic replacement keeps one round-2 route inside the final
scale-twelve vertical halo. -/
theorem ContinuousPlanarPresentation.finalNormalizationRoute_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.toPlanarPresentation.normalizationGridDrawing2
        |>.PolylineInExpandedVerticalBand
          (presentation.toPlanarPresentation.normalizationRoute2 edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.toPlanarPresentation.normalizationGridDrawing2)
      |>.PolylineInExpandedVerticalBand
        (presentation.toPlanarPresentation.finalNormalizationRoute edge) := by
  let planar := presentation.toPlanarPresentation
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (planar.normalizationRoute2 edge) := by
    have unitSteps := presentation.normalizationRoute2_unitSteps
      wellFormed degree member
    exact unitSteps.imp fun _ _ step => step.isAxisAligned
  have sourceAnchorInside :=
    planar.normalizationPosition2_inExpandedVerticalBand
      endpointMembers.1
  have targetAnchorInside :=
    planar.normalizationTarget2_inExpandedVerticalBand
      horizontal member
  have sourceTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inExpandedVerticalBand
      sourceAnchorInside
      (secondRotationActive planar edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).secondNormalizedPort planar)
  have targetTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inExpandedVerticalBand
      targetAnchorInside
      (secondRotationActive planar edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).secondNormalizedPort planar)
  change
    (vertexNormalizationMagnifiedUnitDrawing
      planar.normalizationGridDrawing2)
      |>.PolylineInExpandedVerticalBand
        (planar.finalNormalizationRoute edge)
  unfold PlanarPresentation.finalNormalizationRoute
  apply normalizeRouteWithTemplates_inExpandedVerticalBand
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.finalNormalizationTemplate,
      ContractedEndpoint.vertex] using sourceTemplateInside
  · simpa [ContractedEndpoint.finalNormalizationTemplate,
      ContractedEndpoint.vertex] using targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes
