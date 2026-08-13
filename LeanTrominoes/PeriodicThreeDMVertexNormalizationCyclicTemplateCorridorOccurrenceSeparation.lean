/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicIncidentCorridorSeparation

/-!
# Lifted cyclic template--corridor separation

For the first cyclic round, every lifted template--corridor pairing is again
source-incident, target-incident, or remote.  The incident cases use the local
incoming-port half-plane theorem, while complete separation of the first
intermediate drawing handles the remote case.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- A first-stage endpoint center is a listed endpoint of the lifted
first-round route owned by that syntactic endpoint. -/
theorem ContinuousPlanarPresentation.normalizationEndpointOccurrencePosition1_mem_ownRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    planar.normalizationEndpointOccurrencePosition1
        endpoint routeTranslate ∈
      planar.normalizationRouteOccurrence1
        endpoint.edge routeTranslate := by
  dsimp only
  have endpoints :=
    presentation.normalizationRouteOccurrence1_normalizationEndpoints
      degree (endpoint.edge_mem_of_mem endpointMember) routeTranslate
  cases endpoint with
  | source edge =>
      exact List.mem_of_mem_head? endpoints.1
  | target edge =>
      exact List.mem_of_mem_getLast? endpoints.2

/-- Source-incident specialization for a different first-stage endpoint
occurrence at the same lifted vertex. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrence_strictlyAvoids_incidentSourceTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {endpointTranslate routeTranslate : Cell}
    (sameKey : endpoint.occurrenceKey endpointTranslate =
      (ContractedEndpoint.source edge).occurrenceKey routeTranslate)
    (differentOccurrences : (endpoint.edge, endpointTranslate) ≠
      (edge, routeTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationCorridorOccurrence edge routeTranslate)
      (planar.secondNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let sourcePosition :=
    planar.normalizationEndpointOccurrencePosition1
      sourceEndpoint routeTranslate
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree edgeMember routeTranslate
  have routeSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have routeOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  obtain ⟨first, second, rest, routeEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  have geometry :=
    presentation.normalizationRouteOccurrence1_endpointGeometry
      degree edgeMember routeTranslate
  change oldRoute.head? = some sourcePosition ∧
    oldRoute.tail.head? = some (Cell.add sourcePosition
      (sourceEndpoint.firstNormalizedPort planar).direction.step) ∧
    oldRoute.getLast? = some
      (planar.normalizationEndpointOccurrencePosition1
        (.target edge) routeTranslate) ∧
    oldRoute.reverse.tail.head? = some (Cell.add
      (planar.normalizationEndpointOccurrencePosition1
        (.target edge) routeTranslate)
      ((ContractedEndpoint.target edge).firstNormalizedPort
        planar).direction.step) at geometry
  have firstEqual : first = sourcePosition := by
    rw [routeEquation] at geometry
    exact Option.some.inj geometry.1
  subst first
  rw [routeEquation] at routeSimple routeOrthogonal geometry
  have sourceDirection :
      AxisDirection.between sourcePosition second =
        (sourceEndpoint.firstNormalizedPort planar).direction := by
    have secondEqual : second = Cell.add sourcePosition
        (sourceEndpoint.firstNormalizedPort planar).direction.step :=
      Option.some.inj geometry.2.1
    rw [secondEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine
        (sourceEndpoint.firstNormalizedPort planar))
  have verticesEqual : endpoint.vertex = sourceEndpoint.vertex :=
    congrArg Prod.fst sameKey
  have positionsEqual :=
    planar.normalizationEndpointOccurrencePosition1_eq_of_key_eq sameKey
  have endpointsDifferent : endpoint ≠ sourceEndpoint := by
    intro equal
    subst endpoint
    have translatesEqual :=
      sourceEndpoint.occurrenceKey_injective_for_endpoint sameKey
    exact differentOccurrences (Prod.ext rfl translatesEqual)
  have portsDifferent := endpoint.firstNormalizedPort_ne
    presentation wellFormed degree endpointMember sourceMember
      endpointsDifferent verticesEqual
  have incident :=
    trimmedMagnifiedRoute_strictlyAvoids_incident_otherRotationRoundTemplate
      sourcePosition second rest routeSimple routeOrthogonal
      (sourceEndpoint.firstNormalizedPort planar)
      (endpoint.firstNormalizedPort planar)
      sourceDirection
      (firstRotationActive planar sourceEndpoint.vertex)
      (by simpa [verticesEqual] using portsDifferent)
  rw [← routeEquation] at incident
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute oldRoute)
    (normalizationTemplateAt
      (planar.normalizationEndpointOccurrencePosition1
        endpoint endpointTranslate)
      (rotationRoundPortAndRoute
        (firstRotationActive planar endpoint.vertex)
        (endpoint.firstNormalizedPort planar)).2)
  rw [positionsEqual, verticesEqual]
  exact incident

/-- Target-incident specialization, symmetric to the source result. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrence_strictlyAvoids_incidentTargetTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {endpointTranslate routeTranslate : Cell}
    (sameKey : endpoint.occurrenceKey endpointTranslate =
      (ContractedEndpoint.target edge).occurrenceKey routeTranslate)
    (differentOccurrences : (endpoint.edge, endpointTranslate) ≠
      (edge, routeTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationCorridorOccurrence edge routeTranslate)
      (planar.secondNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  let targetEndpoint := ContractedEndpoint.target edge
  let targetPosition :=
    planar.normalizationEndpointOccurrencePosition1
      targetEndpoint routeTranslate
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree edgeMember routeTranslate
  have routeSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have routeOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  obtain ⟨leading, before, last, routeEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have geometry :=
    presentation.normalizationRouteOccurrence1_endpointGeometry
      degree edgeMember routeTranslate
  change oldRoute.head? = some
      (planar.normalizationEndpointOccurrencePosition1
        (.source edge) routeTranslate) ∧
    oldRoute.tail.head? = some (Cell.add
      (planar.normalizationEndpointOccurrencePosition1
        (.source edge) routeTranslate)
      ((ContractedEndpoint.source edge).firstNormalizedPort
        planar).direction.step) ∧
    oldRoute.getLast? = some targetPosition ∧
    oldRoute.reverse.tail.head? = some (Cell.add targetPosition
      (targetEndpoint.firstNormalizedPort planar).direction.step)
      at geometry
  have lastEqual : last = targetPosition := by
    rw [routeEquation] at geometry
    apply Option.some.inj
    simpa using geometry.2.2.1
  subst last
  rw [routeEquation] at routeSimple routeOrthogonal geometry
  have targetDirection :
      AxisDirection.between targetPosition before =
        (targetEndpoint.firstNormalizedPort planar).direction := by
    have beforeEqual : before = Cell.add targetPosition
        (targetEndpoint.firstNormalizedPort planar).direction.step := by
      apply Option.some.inj
      simpa using geometry.2.2.2
    rw [beforeEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine
        (targetEndpoint.firstNormalizedPort planar))
  have verticesEqual : endpoint.vertex = targetEndpoint.vertex :=
    congrArg Prod.fst sameKey
  have positionsEqual :=
    planar.normalizationEndpointOccurrencePosition1_eq_of_key_eq sameKey
  have endpointsDifferent : endpoint ≠ targetEndpoint := by
    intro equal
    subst endpoint
    have translatesEqual :=
      targetEndpoint.occurrenceKey_injective_for_endpoint sameKey
    exact differentOccurrences (Prod.ext rfl translatesEqual)
  have portsDifferent := endpoint.firstNormalizedPort_ne
    presentation wellFormed degree endpointMember targetMember
      endpointsDifferent verticesEqual
  have incident :=
    trimmedMagnifiedRoute_strictlyAvoids_incident_otherRotationRoundTemplate_at_target
      leading before targetPosition routeSimple routeOrthogonal
      (targetEndpoint.firstNormalizedPort planar)
      (endpoint.firstNormalizedPort planar)
      targetDirection
      (firstRotationActive planar targetEndpoint.vertex)
      (by simpa [verticesEqual] using portsDifferent)
  rw [← routeEquation] at incident
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute oldRoute)
    (normalizationTemplateAt
      (planar.normalizationEndpointOccurrencePosition1
        endpoint endpointTranslate)
      (rotationRoundPortAndRoute
        (firstRotationActive planar endpoint.vertex)
        (endpoint.firstNormalizedPort planar)).2)
  rw [positionsEqual, verticesEqual]
  exact incident

/-- If a cyclic template center is neither endpoint of another first-round
route occurrence, complete old-route separation makes it remote from the
whole corridor. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrence_strictlyAvoids_remoteTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {endpointTranslate routeTranslate : Cell}
    (differentOccurrences : (endpoint.edge, endpointTranslate) ≠
      (edge, routeTranslate))
    (sourceKeyDifferent : endpoint.occurrenceKey endpointTranslate ≠
      (ContractedEndpoint.source edge).occurrenceKey routeTranslate)
    (targetKeyDifferent : endpoint.occurrenceKey endpointTranslate ≠
      (ContractedEndpoint.target edge).occurrenceKey routeTranslate) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationCorridorOccurrence edge routeTranslate)
      (planar.secondNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let templateRoute := planar.normalizationRouteOccurrence1
    endpoint.edge endpointTranslate
  let corridorRoute := planar.normalizationRouteOccurrence1
    edge routeTranslate
  let position := planar.normalizationEndpointOccurrencePosition1
    endpoint endpointTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  have templateEdgeMember := endpoint.edge_mem_of_mem endpointMember
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have oldAvoid : RoutesAvoidEachOther templateRoute corridorRoute :=
    presentation.normalizationRouteOccurrences1_avoidEachOther
      wellFormed degree separated sourceSimple
      templateEdgeMember edgeMember endpointTranslate routeTranslate
      differentOccurrences
  have positionMember : position ∈ templateRoute :=
    presentation.normalizationEndpointOccurrencePosition1_mem_ownRoute
      degree endpointMember endpointTranslate
  have corridorEndpoints :=
    presentation.normalizationRouteOccurrence1_normalizationEndpoints
      degree edgeMember routeTranslate
  have oldPointsAvoid : ∀ point ∈ corridorRoute, point ≠ position := by
    intro point pointMember equal
    rcases List.mem_iff_get.mp positionMember with
      ⟨positionIndex, positionAt⟩
    rcases List.mem_iff_get.mp pointMember with
      ⟨pointIndex, pointAt⟩
    have indexedEqual :
        templateRoute.get positionIndex = corridorRoute.get pointIndex :=
      positionAt.trans (equal.symm.trans pointAt.symm)
    have contacts := oldAvoid.2.2.2
      positionIndex pointIndex indexedEqual
    rw [positionAt, pointAt] at contacts
    rcases contacts.2 with atHead | atLast
    · have pointAtSource : point =
          planar.normalizationEndpointOccurrencePosition1
            sourceEndpoint routeTranslate :=
        Option.some.inj (atHead.symm.trans corridorEndpoints.1)
      have positionsEqual : position =
          planar.normalizationEndpointOccurrencePosition1
            sourceEndpoint routeTranslate :=
        equal.symm.trans pointAtSource
      exact sourceKeyDifferent
        (planar.normalizationEndpointOccurrencePosition1_injective
          (endpoint.vertex_mem_of_mem endpointMember)
          (sourceEndpoint.vertex_mem_of_mem sourceMember)
          positionsEqual)
    · have pointAtTarget : point =
          planar.normalizationEndpointOccurrencePosition1
            targetEndpoint routeTranslate :=
        Option.some.inj (atLast.symm.trans corridorEndpoints.2)
      have positionsEqual : position =
          planar.normalizationEndpointOccurrencePosition1
            targetEndpoint routeTranslate :=
        equal.symm.trans pointAtTarget
      exact targetKeyDifferent
        (planar.normalizationEndpointOccurrencePosition1_injective
          (endpoint.vertex_mem_of_mem endpointMember)
          (targetEndpoint.vertex_mem_of_mem targetMember)
          positionsEqual)
  have oldSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments corridorRoute,
        segment.IsAxisAligned → ¬segment.Contains position := by
    intro segment segmentMember _aligned contains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          contains with
      interior | atEndpoint
    · exact oldAvoid.firstPointsAvoid_of_mem
        position positionMember segment segmentMember interior
    · have segmentEndpoints :=
        gridPolylineSegments_endpoints_mem segmentMember
      rcases atEndpoint with atStart | atFinish
      · exact (oldPointsAvoid segment.start segmentEndpoints.1) atStart.symm
      · exact (oldPointsAvoid segment.finish segmentEndpoints.2) atFinish.symm
  have corridorOrthogonal : OrthogonalPolyline corridorRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  have remote :=
    trimmedMagnifiedRoute_strictlyAvoids_rotationRoundTemplate
      corridorOrthogonal oldPointsAvoid oldSegmentsAvoid
      (firstRotationActive planar endpoint.vertex)
      (endpoint.firstNormalizedPort planar)
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute corridorRoute)
    (normalizationTemplateAt position
      (rotationRoundPortAndRoute
        (firstRotationActive planar endpoint.vertex)
        (endpoint.firstNormalizedPort planar)).2)
  exact remote

/-- Complete cyclic template--corridor classification for distinct
first-round route occurrences. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {endpointTranslate routeTranslate : Cell}
    (differentOccurrences : (endpoint.edge, endpointTranslate) ≠
      (edge, routeTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationCorridorOccurrence edge routeTranslate)
      (planar.secondNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  by_cases sourceKeyEqual : endpoint.occurrenceKey endpointTranslate =
      sourceEndpoint.occurrenceKey routeTranslate
  · exact
      presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_incidentSourceTemplate
        wellFormed degree separated sourceSimple endpointMember edgeMember
        sourceKeyEqual differentOccurrences
  · by_cases targetKeyEqual : endpoint.occurrenceKey endpointTranslate =
        targetEndpoint.occurrenceKey routeTranslate
    · exact
        presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_incidentTargetTemplate
          wellFormed degree separated sourceSimple endpointMember edgeMember
          targetKeyEqual differentOccurrences
    · exact
        presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_remoteTemplate
          wellFormed degree separated sourceSimple endpointMember edgeMember
          differentOccurrences sourceKeyEqual targetKeyEqual

/-- Symmetric orientation used when the cyclic template is the first piece
in an assembly pairing. -/
theorem ContinuousPlanarPresentation.secondNormalizationTemplateOccurrence_strictlyAvoids_corridorOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {endpointTranslate routeTranslate : Cell}
    (differentOccurrences : (endpoint.edge, endpointTranslate) ≠
      (edge, routeTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationTemplateOccurrence
        endpoint endpointTranslate)
      (planar.secondNormalizationCorridorOccurrence edge routeTranslate) := by
  dsimp only
  exact
    (presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
      wellFormed degree separated sourceSimple endpointMember edgeMember
      differentOccurrences).symm

end PeriodicThreeDM
end LeanTrominoes
