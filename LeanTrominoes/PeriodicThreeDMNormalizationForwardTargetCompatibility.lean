import LeanTrominoes.PeriodicThreeDMContractionCoverage
import LeanTrominoes.PeriodicThreeDMNormalizationForwardSourceCompatibility

/-!
# Forward-orientation compatibility at contracted-edge targets

The final route is based at its source occurrence, while its target vertex is
looked up at the source translate plus the contracted edge offset.  This
module reconciles those two period coordinates and proves compatibility
between the last routing cell and the target vertex.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A route site points forward toward its successor with the owning edge's
source value. -/
theorem routeSiteInward_toward_after
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (before current after translate : Cell)
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite) :
    routeSiteInward values edge before current after translate
        (Side.ofAxisDirection (AxisDirection.between current after)) =
      edge.sourceInward values translate := by
  have incomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep incoming
  have outgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep outgoing
  have backward :
      AxisDirection.between current before =
        (AxisDirection.between before current).opposite :=
    AxisDirection.between_reverse_eq_opposite incomingGenuine
  have backwardGenuine :
      (AxisDirection.between current before).IsGenuine := by
    rw [backward]
    exact AxisDirection.opposite_isGenuine incomingGenuine
  have directionsDifferent :
      AxisDirection.between current before ≠
        AxisDirection.between current after := by
    rw [backward]
    exact Ne.symm noReverse
  have sidesDifferent :
      Side.ofAxisDirection (AxisDirection.between current before) ≠
        Side.ofAxisDirection (AxisDirection.between current after) :=
    Side.ofAxisDirection_injective_of_genuine
      backwardGenuine outgoingGenuine directionsDifferent
  simp [routeSiteInward, Ne.symm sidesDifferent]

/-- Distinct Booleans are complements. -/
theorem bool_eq_not_of_ne (first second : Bool) (different : first ≠ second) :
    first = !second := by
  cases first <;> cases second <;> simp_all

/-- Translating the stored target occurrence by a source period translate is
the same point as translating the base target vertex by the source translate
plus the contracted-edge offset. -/
theorem PlanarPresentation.finalTargetOccurrence_add_periodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (sourceTranslate : Cell) :
    Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        (Cell.scale (presentation.finalNormalizationPeriod : Int)
          sourceTranslate) =
      Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.target)
        (Cell.scale (presentation.finalNormalizationPeriod : Int)
          (Cell.add sourceTranslate edge.toPeriodicEdge.offset)) := by
  rw [presentation.finalTargetOccurrence_eq]
  rw [presentation.finalScaledPeriodTranslation_eq]
  rcases presentation.finalNormalizationPosition edge.toPeriodicEdge.target with
    ⟨targetX, targetY⟩
  rcases sourceTranslate with ⟨sourceX, sourceY⟩
  rcases edge.toPeriodicEdge.offset with ⟨offsetX, offsetY⟩
  simp only [Cell.add, Cell.scale, Prod.mk.injEq]
  constructor <;> ring

/-- The geometric side of the last routing cell that faces its target is the
opposite of the target endpoint's normalized vertex port. -/
theorem PlanarPresentation.targetAdjacent_forwardSide
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge)
    (firstStep : AxisDirection.IsUnitAxisStep
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.target edge).finalNormalizedPort
          presentation).direction.step)) :
    Side.ofAxisDirection
        (AxisDirection.between
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))) =
      ((ContractedEndpoint.target edge).finalNormalizedPort
        presentation).side.opposite := by
  let port :=
    (ContractedEndpoint.target edge).finalNormalizedPort presentation
  have outward :
      AxisDirection.between
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            port.direction.step) =
        port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have inward :
      AxisDirection.between
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            port.direction.step)
          (normalizeVertexPosition (presentation.normalizationTarget2 edge)) =
        port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [outward]
  rw [inward]
  rw [Side.ofAxisDirection_opposite
    (CanonicalVertexPort.direction_isGenuine port)]
  simp [port]

/-- At every lifted occurrence, a contracted edge's target-vertex port has
the value opposite to the target-adjacent routing-cell port. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_target_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
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
    let location := reflectedLocation
      (Cell.add targetOccurrence
        (Cell.scale (planar.finalNormalizationPeriod : Int) sourceTranslate))
    presentation.forwardDrawingOrientation values location port.side =
      !(presentation.forwardDrawingOrientation values
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
    planar.finalOrientationSite_vertex_mem vertexMember
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
      (rasterLocation planar.finalNormalizationPeriod adjacentPoint,
        FinalOrientationSite.route edge third adjacentPoint targetOccurrence) ∈
          planar.finalOrientationSites := by
    apply planar.finalOrientationSite_route_mem edgeMember reverseRest.reverse
      third adjacentPoint targetOccurrence []
    simpa using routeEquation
  have targetOccurrenceEq :
      Cell.add targetOccurrence
          (Cell.scale (planar.finalNormalizationPeriod : Int) sourceTranslate) =
        Cell.add targetPoint
          (Cell.scale (planar.finalNormalizationPeriod : Int)
            targetTranslate) := by
    simpa [targetOccurrence, targetPoint, targetTranslate] using
      planar.finalTargetOccurrence_add_periodTranslation edge sourceTranslate
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor
          (reflectedLocation
            (Cell.add targetOccurrence
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                sourceTranslate)))
          port.side =
        reflectedLocation
          (Cell.add adjacentPoint
            (Cell.scale (planar.finalNormalizationPeriod : Int)
              sourceTranslate)) := by
    simpa [adjacentPoint] using
      latticeNeighbor_reflected_periodOccurrence
        planar.finalNormalizationPeriod targetOccurrence sourceTranslate port.side
  rw [neighborEq]
  have vertexValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values vertexSiteMember targetTranslate port.side
  have routeValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values routeSiteMember sourceTranslate port.side.opposite
  have vertexValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add targetOccurrence
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                sourceTranslate))) port.side =
        (FinalOrientationSite.vertex endpoint.vertex).inward
          planar values targetTranslate port.side := by
    rw [targetOccurrenceEq]
    simpa [FinalOrientationSite.point, endpoint, ContractedEndpoint.vertex,
      targetPoint] using vertexValue
  have routeValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add adjacentPoint
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                sourceTranslate))) port.side.opposite =
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
