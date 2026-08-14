/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripRouteRasterization

/-!
# Source-endpoint matching in the normalized 3DM strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The source-adjacent strip routing cell exposes the owning edge's color on
the side facing its source vertex. -/
theorem PlanarPresentation.finalStripCellTypeAt_sourceAdjacent_portColor
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.finalStripCellTypeAt
      (stripRasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step))).portColor
      ((ContractedEndpoint.source edge).finalNormalizedPort
        presentation).side.opposite = some edge.color := by
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_sourceTriple edge
  have assignmentMember :
      (stripRasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          third edge.color) ∈
        stripRouteInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
    rw [routeEquation]
    simp [stripRouteInteriorAssignments]
  rw [presentation.finalStripCellTypeAt_routeInterior collisionFree edgeMember
    assignmentMember]
  rw [routingCellTypeAt_portColor firstStep secondStep noReverse]
  let port := (ContractedEndpoint.source edge).finalNormalizedPort presentation
  have forward : AxisDirection.between
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
      (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        port.direction.step) = port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have backward : AxisDirection.between
      (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        port.direction.step)
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source) =
      port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [forward]
  have backwardSide : Side.ofAxisDirection
      (AxisDirection.between
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          port.direction.step)
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)) =
      port.side.opposite := by
    rw [backward]
    rw [Side.ofAxisDirection_opposite
      (CanonicalVertexPort.direction_isGenuine port)]
    simp
  simp [port, backwardSide]

/-- Every listed edge's source vertex and source-adjacent strip routing cell
expose the same color on their common side. -/
theorem PlanarPresentation.finalStripCellTypeAt_source_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort
      presentation.toPlanarPresentation
    (presentation.toPlanarPresentation.finalStripCellTypeAt
      (stripRasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (presentation.toPlanarPresentation.finalNormalizationPosition
          edge.toPeriodicEdge.source))).portColor port.side =
    (presentation.toPlanarPresentation.finalStripCellTypeAt
      (stripRasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (Cell.add
          (presentation.toPlanarPresentation.finalNormalizationPosition
            edge.toPeriodicEdge.source)
          port.direction.step))).portColor port.side.opposite := by
  dsimp only
  let endpoint := ContractedEndpoint.source edge
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp only [endpoint, contractedEndpoints, List.mem_flatMap]
    exact ⟨edge, edgeMember, by simp⟩
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have sourceVertex : endpoint.vertex = edge.toPeriodicEdge.source := rfl
  rw [← sourceVertex]
  rw [presentation.toPlanarPresentation.finalStripCellTypeAt_vertex
    collisionFree vertexMember]
  rw [PlanarPresentation.finalVertexCellType_portColor_endpoint
    (presentation := presentation) wellFormed degree endpointMember]
  simpa [endpoint, sourceVertex, ContractedEndpoint.color,
    ContractedEndpoint.edge] using
    (PlanarPresentation.finalStripCellTypeAt_sourceAdjacent_portColor
      (presentation := presentation.toPlanarPresentation)
      collisionFree edgeMember).symm

end PeriodicThreeDM
end LeanTrominoes
