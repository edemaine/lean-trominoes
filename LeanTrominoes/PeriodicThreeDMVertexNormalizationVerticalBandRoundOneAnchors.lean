/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMOneDimensionalContraction
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRoutes
import LeanTrominoes.PeriodicGridDrawingVerticalBand

/-!
# Vertical-band bounds for first-round normalization anchors
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained contracted vertex position lies in the contracted
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition0_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.contractedDrawing.PositionInExpandedVerticalBand
      (presentation.normalizationPosition0 vertex) := by
  apply
    PeriodicGridDrawing.positionInExpandedVerticalBand_of_fundamentalSquare
  apply presentation.contractedPositions_in_fundamental_square
  unfold PlanarPresentation.normalizationPosition0
  rw [presentation.contractedDrawing_vertexPosition member]
  rw [presentation.contractedVertexPositions_eq_map]
  exact List.mem_map.mpr ⟨vertex, member, rfl⟩

/-- The target occurrence of an emitted horizontal contracted edge has the
same vertical coordinate as its retained target prototype, and hence lies
in the old open halo. -/
theorem PlanarPresentation.normalizationTarget0_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.contractedDrawing.PositionInExpandedVerticalBand
      (presentation.normalizationTarget0 edge) := by
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have targetInside :=
    presentation.normalizationPosition0_inExpandedVerticalBand
      endpointMembers.2
  apply
    PeriodicGridDrawing.positionInExpandedVerticalBand_of_vertical_eq
      targetInside
  have edgeHorizontal :=
    contractedEdge_offset_vertical_eq_zero horizontal member
  simp [PlanarPresentation.normalizationTarget0,
    PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.add, edgeHorizontal]

end PeriodicThreeDM
end LeanTrominoes
