/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardTargetCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardSourceCompatibility

/-!
# Forward-orientation compatibility at strip target endpoints
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- In a one-dimensional instance, translating the routed target occurrence
by a source strip block equals translating the base target vertex by the
source block plus the contracted-edge offset. -/
theorem PlanarPresentation.finalTargetOccurrence_add_stripPeriodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    Cell.add
        (stripReflectedLocation presentation.finalNormalizationPeriod
          (normalizeVertexPosition (presentation.normalizationTarget2 edge)))
        (presentation.stripPeriodTranslation sourceTranslate) =
      Cell.add
        (stripReflectedLocation presentation.finalNormalizationPeriod
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.target))
        (presentation.stripPeriodTranslation
          (Cell.add sourceTranslate edge.toPeriodicEdge.offset)) := by
  have verticalZero :=
    contractedEdge_offset_vertical_eq_zero horizontal edgeMember
  have offsetEquation : edge.toPeriodicEdge.offset =
      (edge.toPeriodicEdge.offset.1, 0) := by
    apply Prod.ext
    · rfl
    · exact verticalZero
  rw [presentation.finalTargetOccurrence_eq]
  rw [presentation.finalScaledPeriodTranslation_eq]
  rw [offsetEquation]
  rcases presentation.finalNormalizationPosition edge.toPeriodicEdge.target with
    ⟨targetX, targetY⟩
  rcases sourceTranslate with ⟨sourceX, sourceY⟩
  simp only [stripReflectedLocation, PlanarPresentation.stripPeriodTranslation,
    Cell.add, Cell.scale, Prod.mk.injEq]
  constructor <;> ring

/-- At every rectangular block occurrence, a contracted edge's target vertex
port is opposite to its target-adjacent strip routing-cell port. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_target_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let endpoint := ContractedEndpoint.target edge
    let port := endpoint.finalNormalizedPort planar
    let targetOccurrence :=
      normalizeVertexPosition (planar.normalizationTarget2 edge)
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod targetOccurrence)
      (planar.stripPeriodTranslation sourceTranslate)
    presentation.forwardStripDrawingOrientation values location port.side =
      !(presentation.forwardStripDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location port.side)
        port.side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let endpoint := ContractedEndpoint.target edge
  let port := endpoint.finalNormalizedPort planar
  let targetPoint :=
    planar.finalNormalizationPosition edge.toPeriodicEdge.target
  let targetOccurrence :=
    normalizeVertexPosition (planar.normalizationTarget2 edge)
  let adjacentPoint := Cell.add targetOccurrence port.direction.step
  let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp [endpoint, contractedEndpoints, edgeMember]
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have vertexSiteMember :=
    planar.finalStripOrientationSite_vertex_mem vertexMember
  obtain ⟨third, reverseRest, reverseEquation, firstStep, secondStep,
      reverseNoReverse⟩ :=
    planar.exists_finalNormalizationRoute_targetTriple edge
  have forwardEquation := congrArg List.reverse reverseEquation
  simp only [List.reverse_reverse, List.reverse_cons] at forwardEquation
  have routeEquation :
      planar.finalNormalizationRoute edge =
        reverseRest.reverse ++ [third, adjacentPoint, targetOccurrence] := by
    simpa [adjacentPoint, targetOccurrence, port] using forwardEquation
  have routeSiteMember :
      (stripRasterLocation planar.finalNormalizationPeriod adjacentPoint,
        FinalOrientationSite.route edge third adjacentPoint targetOccurrence) ∈
          planar.finalStripOrientationSites := by
    apply planar.finalStripOrientationSite_route_mem edgeMember reverseRest.reverse
      third adjacentPoint targetOccurrence []
    simpa using routeEquation
  have targetOccurrenceEq :
      Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod targetOccurrence)
          (planar.stripPeriodTranslation sourceTranslate) =
        Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod targetPoint)
          (planar.stripPeriodTranslation targetTranslate) := by
    simpa [targetOccurrence, targetPoint, targetTranslate] using
      planar.finalTargetOccurrence_add_stripPeriodTranslation
        horizontal edgeMember sourceTranslate
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod targetOccurrence)
            (planar.stripPeriodTranslation sourceTranslate)) port.side =
        Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod adjacentPoint)
          (planar.stripPeriodTranslation sourceTranslate) := by
    rw [planar.latticeNeighbor_stripPeriodOccurrence]
    rw [axisDirectionOfSide_stripCanonicalPort_side]
  rw [neighborEq]
  have vertexValue :=
    presentation.forwardStripDrawingOrientation_periodOccurrence
      wellFormed degree horizontal sourceInside collisionFree values
      vertexSiteMember (translate := targetTranslate) port.side
  have routeValue :=
    presentation.forwardStripDrawingOrientation_periodOccurrence
      wellFormed degree horizontal sourceInside collisionFree values
      routeSiteMember (translate := sourceTranslate) port.side.opposite
  have vertexValue' :
      presentation.forwardStripDrawingOrientation values
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod targetOccurrence)
            (planar.stripPeriodTranslation sourceTranslate)) port.side =
        (FinalOrientationSite.vertex endpoint.vertex).inward
          planar values targetTranslate port.side := by
    rw [targetOccurrenceEq]
    simpa [FinalOrientationSite.point, endpoint, ContractedEndpoint.vertex,
      targetPoint] using vertexValue
  have routeValue' :
      presentation.forwardStripDrawingOrientation values
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod adjacentPoint)
            (planar.stripPeriodTranslation sourceTranslate)) port.side.opposite =
        (FinalOrientationSite.route edge third adjacentPoint targetOccurrence).inward
          planar values sourceTranslate port.side.opposite := by
    simpa [FinalOrientationSite.point] using routeValue
  rw [vertexValue', routeValue']
  simp only [FinalOrientationSite.inward]
  have endpointValue := PlanarPresentation.vertexPortInward_endpoint
    presentation wellFormed degree values endpointMember targetTranslate
  have endpointValue' :
      planar.vertexPortInward values endpoint.vertex targetTranslate port.side =
        endpoint.inwardAtVertexTranslate values targetTranslate := by
    simpa [endpoint, port, ContractedEndpoint.vertex] using endpointValue
  rw [endpointValue']
  have targetEndpointValue :
      endpoint.inwardAtVertexTranslate values targetTranslate =
        edge.targetInward values sourceTranslate := by
    simp [endpoint, targetTranslate,
      ContractedEndpoint.inwardAtVertexTranslate,
      ContractedEdge.targetInwardAtTarget]
  rw [targetEndpointValue]
  have incoming := secondStep.symm
  have outgoing := firstStep.symm
  have noReverse :
      AxisDirection.between adjacentPoint targetOccurrence ≠
        (AxisDirection.between third adjacentPoint).opposite := by
    have firstGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep firstStep
    have secondGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep secondStep
    change
      AxisDirection.between
          (Cell.add
            (normalizeVertexPosition (planar.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              planar).direction.step)
          (normalizeVertexPosition (planar.normalizationTarget2 edge)) ≠
        (AxisDirection.between third
          (Cell.add
            (normalizeVertexPosition (planar.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              planar).direction.step)).opposite
    rw [AxisDirection.between_reverse_eq_opposite firstGenuine]
    rw [AxisDirection.between_reverse_eq_opposite secondGenuine]
    simp only [AxisDirection.opposite_opposite]
    exact Ne.symm reverseNoReverse
  have forwardSide := planar.targetAdjacent_forwardSide edge firstStep
  rw [← forwardSide]
  rw [routeSiteInward_toward_after values edge third adjacentPoint
    targetOccurrence sourceTranslate incoming outgoing noReverse]
  exact bool_eq_not_of_ne _ _
    (Ne.symm
      (contractedEdge_endpointInward_ne problem values valid
        edgeMember sourceTranslate))

end PeriodicThreeDM
end LeanTrominoes
