/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractionGeometry
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandFigureTwoTemplate
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundOneAnchors
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandSplice

/-!
# Vertical-band preservation for one first-round normalized route
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The first Figure 2 replacement keeps one emitted contracted route inside
the scale-twelve vertical halo. -/
theorem PlanarPresentation.normalizationRoute1_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.contractedDrawing.PolylineInExpandedVerticalBand
        (presentation.contractedEdgeRoute edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.contractedDrawing)
      |>.PolylineInExpandedVerticalBand
        (presentation.normalizationRoute1 edge) := by
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (presentation.contractedEdgeRoute edge) := by
    have localMember := member
    simp only [contractedEdges, List.mem_flatMap] at localMember
    rcases localMember with ⟨color, _colorMember, localMember⟩
    simp only [contractedEdgesForColor,
      List.mem_flatMap] at localMember
    rcases localMember with ⟨atom, _atomMember, localMember⟩
    exact presentation.contractedEdgeRoute_orthogonal
      color atom localMember
  have sourceAnchorInside :=
    presentation.normalizationPosition0_inExpandedVerticalBand
      endpointMembers.1
  have targetAnchorInside :=
    presentation.normalizationTarget0_inExpandedVerticalBand
      horizontal member
  have sourceTemplateInside :=
    normalizationTemplateAt_route_inExpandedVerticalBand
      sourceAnchorInside
      (omittedSideAt presentation edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).firstNormalizedPort presentation)
  have targetTemplateInside :=
    normalizationTemplateAt_route_inExpandedVerticalBand
      targetAnchorInside
      (omittedSideAt presentation edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).firstNormalizedPort presentation)
  unfold PlanarPresentation.normalizationRoute1
  apply normalizeRouteWithTemplates_inExpandedVerticalBand
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.firstNormalizationTemplate,
      ContractedEndpoint.vertex] using
      sourceTemplateInside
  · simpa [ContractedEndpoint.firstNormalizationTemplate,
      ContractedEndpoint.vertex] using
      targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes
