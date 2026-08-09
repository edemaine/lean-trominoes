import LeanTrominoes.PeriodicThreeDMVertexNormalizationEndpointColors
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-!
# Rasterized normalized-route endpoints

This module joins the endpoint geometry, endpoint colors, and collision-free
assignment lookup.  It proves that the first routing cell of every listed
normalized edge is emitted by the rasterizer and that its port toward the
source vertex has exactly the owning edge's color.  Consequently the source
vertex and its adjacent routing cell have matching ports.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- A list of length at least three can expose its first three entries. -/
theorem List.exists_eq_cons_cons_cons_of_length_ge_three
    {α : Type*} {items : List α}
    (length : 3 ≤ items.length) :
    ∃ first second third rest,
      items = first :: second :: third :: rest := by
  cases items with
  | nil => simp at length
  | cons first items =>
      cases items with
      | nil => simp at length
      | cons second items =>
          cases items with
          | nil => simp at length
          | cons third rest => exact ⟨first, second, third, rest, rfl⟩

/-- Both choices of final rotation template avoid immediate reversal. -/
theorem rotationRoundPortAndRoute_noImmediateReversal
    (active : Bool) (oldPort : CanonicalVertexPort) :
    AxisDirection.HasNoImmediateReversal
      (rotationRoundPortAndRoute active oldPort).2 := by
  cases active <;> cases oldPort <;>
    simp [rotationRoundPortAndRoute,
      DegreeThreeVertexNormalization.identityRotationRoute,
      DegreeThreeVertexNormalization.clockwiseRotationRoute,
      newPortAfterClockwise,
      AxisDirection.HasNoImmediateReversal,
      AxisDirection.between, AxisDirection.opposite]

/-- Every endpoint's selected final template avoids immediate reversal. -/
theorem ContractedEndpoint.finalNormalizationTemplate_noImmediateReversal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    AxisDirection.HasNoImmediateReversal
      (endpoint.finalNormalizationTemplate presentation) := by
  simpa [ContractedEndpoint.finalNormalizationTemplate] using
    rotationRoundPortAndRoute_noImmediateReversal
      (secondRotationActive presentation endpoint.vertex)
      (endpoint.secondNormalizedPort presentation)

/-- Translation preserves a unit-step chain. -/
theorem normalizationTemplateAt_unitSteps
    (position : Cell) {template : List Cell}
    (unitSteps : template.IsChain AxisDirection.IsUnitAxisStep) :
    (normalizationTemplateAt position template).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold normalizationTemplateAt
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain
      (Cell.add (Cell.scale vertexNormalizationScale position))
  · intro first second (step : AxisDirection.IsUnitAxisStep first second)
    exact AxisDirection.IsUnitAxisStep.translate step _
  · exact unitSteps

/-- The translated final template is literally a prefix of the fully spliced
normalized route. -/
theorem PlanarPresentation.finalNormalizationSourceTemplate_prefix
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    normalizationTemplateAt
        (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
        ((ContractedEndpoint.source edge).finalNormalizationTemplate
          presentation) <+:
      presentation.finalNormalizationRoute edge := by
  unfold PlanarPresentation.finalNormalizationRoute
  unfold normalizeRouteWithTemplates
  exact ⟨_, rfl⟩

/-- The first three points of every final route consist of its normalized
source vertex, the computed adjacent port point, and one further point.  The
two local edges are unit steps and do not immediately reverse. -/
theorem PlanarPresentation.exists_finalNormalizationRoute_sourceTriple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third rest,
      presentation.finalNormalizationRoute edge =
        presentation.finalNormalizationPosition
            edge.toPeriodicEdge.source ::
          Cell.add
              (presentation.finalNormalizationPosition
                edge.toPeriodicEdge.source)
              ((ContractedEndpoint.source edge).finalNormalizedPort
                presentation).direction.step ::
          third :: rest ∧
      AxisDirection.IsUnitAxisStep
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step) ∧
      AxisDirection.IsUnitAxisStep
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step)
        third ∧
      AxisDirection.between
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          third ≠
        (AxisDirection.between
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)).opposite := by
  let endpoint := ContractedEndpoint.source edge
  let localRoute := normalizationTemplateAt
    (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
    (endpoint.finalNormalizationTemplate presentation)
  have geometry := endpoint.finalNormalizationTemplate_geometry presentation
  have localLength : 3 ≤ localRoute.length := by
    simp only [localRoute, normalizationTemplateAt_length]
    exact le_trans (by omega)
      (endpoint.finalNormalizationTemplate_length_ge_four presentation)
  obtain ⟨first, second, third, localRest, localEquation⟩ :=
    List.exists_eq_cons_cons_cons_of_length_ge_three localLength
  have localHead : localRoute.head? =
      some (presentation.finalNormalizationPosition
        edge.toPeriodicEdge.source) := by
    change (normalizationTemplateAt
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      (endpoint.finalNormalizationTemplate presentation)).head? = _
    exact normalizationTemplateAt_head?
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      geometry.1
  have localSecond : localRoute.tail.head? =
      some (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        (endpoint.finalNormalizedPort presentation).direction.step) := by
    change (normalizationTemplateAt
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      (endpoint.finalNormalizationTemplate presentation)).tail.head? = _
    rw [normalizationTemplateAt_tail_head?
      (secondPoint := endpoint.finalNormalizationTemplate_secondPoint
        presentation)]
    simp [PlanarPresentation.finalNormalizationPosition,
      normalizeVertexPosition, Cell.add_assoc]
  rw [localEquation] at localHead localSecond
  have firstEqual : first = presentation.finalNormalizationPosition
      edge.toPeriodicEdge.source := Option.some.inj localHead
  have secondEqual : second = Cell.add
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
      (endpoint.finalNormalizedPort presentation).direction.step := by
    simpa using Option.some.inj localSecond
  subst first
  subst second
  have localUnitSteps : localRoute.IsChain
      AxisDirection.IsUnitAxisStep :=
    normalizationTemplateAt_unitSteps _ geometry.2.2.1
  have localNoReversal :
      AxisDirection.HasNoImmediateReversal localRoute := by
    change AxisDirection.HasNoImmediateReversal
      ((endpoint.finalNormalizationTemplate presentation).map
        (Cell.add (Cell.scale vertexNormalizationScale
          (presentation.normalizationPosition2
            edge.toPeriodicEdge.source))))
    exact (endpoint.finalNormalizationTemplate_noImmediateReversal
      presentation).translate _
  rw [localEquation] at localUnitSteps localNoReversal
  have firstStep := (List.isChain_cons_cons.mp localUnitSteps).1
  have secondStep :=
    (List.isChain_cons_cons.mp
      (List.isChain_cons_cons.mp localUnitSteps).2).1
  have noReverse := localNoReversal.1
  rcases presentation.finalNormalizationSourceTemplate_prefix edge with
    ⟨suffix, prefixEquation⟩
  change localRoute ++ suffix = _ at prefixEquation
  rw [localEquation] at prefixEquation
  refine ⟨third, localRest ++ suffix, ?_, firstStep, secondStep, noReverse⟩
  simpa using prefixEquation.symm

/-- The first route-interior cell of a listed edge is one of the rasterizer's
emitted assignments. -/
theorem PlanarPresentation.sourceAdjacentAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third rest,
      presentation.finalNormalizationRoute edge =
        presentation.finalNormalizationPosition
            edge.toPeriodicEdge.source ::
          Cell.add
              (presentation.finalNormalizationPosition
                edge.toPeriodicEdge.source)
              ((ContractedEndpoint.source edge).finalNormalizedPort
                presentation).direction.step ::
          third :: rest ∧
      (rasterLocation presentation.finalNormalizationPeriod
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
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_sourceTriple edge
  refine ⟨third, rest, routeEquation, ?_⟩
  rw [routeEquation]
  simp [routeInteriorAssignments]

/-- With collision-free assignments, the source-adjacent routing cell has
the owning edge's color on the side facing its source vertex. -/
theorem PlanarPresentation.finalCellTypeAt_sourceAdjacent_portColor
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.finalCellTypeAt
      (rasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step))).portColor
      ((ContractedEndpoint.source edge).finalNormalizedPort
        presentation).side.opposite = some edge.color := by
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_sourceTriple edge
  have assignmentMember :
      (rasterLocation presentation.finalNormalizationPeriod
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
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
    rw [routeEquation]
    simp [routeInteriorAssignments]
  rw [presentation.finalCellTypeAt_routeInterior collisionFree edgeMember
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

/-- Every listed edge's source vertex and source-adjacent routing cell expose
the same color on their common side. -/
theorem PlanarPresentation.finalCellTypeAt_source_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort
      presentation.toPlanarPresentation
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (presentation.toPlanarPresentation.finalNormalizationPosition
          edge.toPeriodicEdge.source))).portColor port.side =
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
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
  rw [presentation.toPlanarPresentation.finalCellTypeAt_vertex
    collisionFree vertexMember]
  rw [PlanarPresentation.finalVertexCellType_portColor_endpoint
    (presentation := presentation) wellFormed degree endpointMember]
  simpa [endpoint, sourceVertex, ContractedEndpoint.color,
    ContractedEndpoint.edge] using
    (PlanarPresentation.finalCellTypeAt_sourceAdjacent_portColor
      (presentation := presentation.toPlanarPresentation)
      collisionFree edgeMember).symm

end PeriodicThreeDM
end LeanTrominoes
