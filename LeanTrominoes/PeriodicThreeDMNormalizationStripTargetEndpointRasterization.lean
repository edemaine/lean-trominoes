/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripSourceEndpointRasterization

/-!
# Target-endpoint matching in the normalized 3DM strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A target-adjacent triple displayed in the reversed route emits the
corresponding strip assignment during the original forward traversal. -/
theorem PlanarPresentation.targetAdjacentStripAssignment_mem_of_reverse_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) {third : Cell} {reverseRest : List Cell}
    (reverseEquation :
      (presentation.finalNormalizationRoute edge).reverse =
        normalizeVertexPosition (presentation.normalizationTarget2 edge) ::
          Cell.add
              (normalizeVertexPosition (presentation.normalizationTarget2 edge))
              ((ContractedEndpoint.target edge).finalNormalizedPort
                presentation).direction.step ::
          third :: reverseRest) :
    (stripRasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step),
      routingCellTypeAt third
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step)
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        edge.color) ∈
      stripRouteInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge) := by
  have forwardEquation := congrArg List.reverse reverseEquation
  simp only [List.reverse_reverse, List.reverse_cons] at forwardEquation
  let suffix := [third,
    Cell.add
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      ((ContractedEndpoint.target edge).finalNormalizedPort
        presentation).direction.step,
    normalizeVertexPosition (presentation.normalizationTarget2 edge)]
  have suffixLength : 3 ≤ suffix.length := by simp [suffix]
  have suffixAssignment :
      (stripRasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt third
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          edge.color) ∈
        stripRouteInteriorAssignments presentation.finalNormalizationPeriod
          edge.color suffix := by
    simp [suffix, stripRouteInteriorAssignments]
  rw [show presentation.finalNormalizationRoute edge =
    reverseRest.reverse ++ suffix by simpa [suffix] using forwardEquation]
  exact stripRouteInteriorAssignments_subset_append _ _ _ _
    suffixLength _ suffixAssignment

/-- The target-adjacent strip routing cell exposes the owning edge's color
on the side facing its periodic target occurrence. -/
theorem PlanarPresentation.finalStripCellTypeAt_targetAdjacent_portColor
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.finalStripCellTypeAt
      (stripRasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step))).portColor
      ((ContractedEndpoint.target edge).finalNormalizedPort
        presentation).side.opposite = some edge.color := by
  obtain ⟨third, reverseRest, reverseEquation, firstStep, secondStep,
      reverseNoReverse⟩ :=
    presentation.exists_finalNormalizationRoute_targetTriple edge
  have assignmentMember :=
    presentation.targetAdjacentStripAssignment_mem_of_reverse_eq edge
      reverseEquation
  rw [presentation.finalStripCellTypeAt_routeInterior collisionFree edgeMember
    assignmentMember]
  have incoming := secondStep.symm
  have outgoing := firstStep.symm
  have noReverse : AxisDirection.between
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.target edge).finalNormalizedPort
          presentation).direction.step)
      (normalizeVertexPosition (presentation.normalizationTarget2 edge)) ≠
    (AxisDirection.between third
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.target edge).finalNormalizedPort
          presentation).direction.step)).opposite := by
    have firstGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep firstStep
    have secondGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep secondStep
    rw [AxisDirection.between_reverse_eq_opposite firstGenuine]
    rw [AxisDirection.between_reverse_eq_opposite secondGenuine]
    simp only [AxisDirection.opposite_opposite]
    exact Ne.symm reverseNoReverse
  rw [routingCellTypeAt_portColor incoming outgoing noReverse]
  let port := (ContractedEndpoint.target edge).finalNormalizedPort presentation
  have forward : AxisDirection.between
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        port.direction.step) = port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have backward : AxisDirection.between
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        port.direction.step)
      (normalizeVertexPosition (presentation.normalizationTarget2 edge)) =
      port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [forward]
  have backwardSide : Side.ofAxisDirection
      (AxisDirection.between
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          port.direction.step)
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))) =
      port.side.opposite := by
    rw [backward]
    rw [Side.ofAxisDirection_opposite
      (CanonicalVertexPort.direction_isGenuine port)]
    simp
  simp [port, backwardSide]

/-- Every listed edge's target vertex and target-adjacent strip routing cell
expose the same color on their common side. -/
theorem PlanarPresentation.finalStripCellTypeAt_target_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let endpoint := ContractedEndpoint.target edge
    let port := endpoint.finalNormalizedPort
      presentation.toPlanarPresentation
    (presentation.toPlanarPresentation.finalStripCellTypeAt
      (stripRasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (presentation.toPlanarPresentation.finalNormalizationPosition
          edge.toPeriodicEdge.target))).portColor port.side =
    (presentation.toPlanarPresentation.finalStripCellTypeAt
      (stripRasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition
            (presentation.toPlanarPresentation.normalizationTarget2 edge))
          port.direction.step))).portColor port.side.opposite := by
  dsimp only
  let endpoint := ContractedEndpoint.target edge
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp only [endpoint, contractedEndpoints, List.mem_flatMap]
    exact ⟨edge, edgeMember, by simp⟩
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have targetVertex : endpoint.vertex = edge.toPeriodicEdge.target := rfl
  rw [← targetVertex]
  rw [presentation.toPlanarPresentation.finalStripCellTypeAt_vertex
    collisionFree vertexMember]
  rw [PlanarPresentation.finalVertexCellType_portColor_endpoint
    (presentation := presentation) wellFormed degree endpointMember]
  simpa [endpoint, targetVertex, ContractedEndpoint.color,
    ContractedEndpoint.edge] using
    (PlanarPresentation.finalStripCellTypeAt_targetAdjacent_portColor
      (presentation := presentation.toPlanarPresentation)
      collisionFree edgeMember).symm

end PeriodicThreeDM
end LeanTrominoes
