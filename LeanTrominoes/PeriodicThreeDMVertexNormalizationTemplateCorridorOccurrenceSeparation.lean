import LeanTrominoes.PeriodicThreeDMVertexNormalizationCorridorOccurrenceSeparation
import LeanTrominoes.PeriodicThreeDMVertexNormalizationIncidentCorridorSeparation

/-!
# Lifted template--corridor separation

For a template occurrence belonging to one contracted route and the trimmed
corridor belonging to another, there are only three cases.  The template
center is the corridor's source endpoint, its target endpoint, or neither.
The first two cases use the directional incident-corridor lemmas; the last
uses complete old-route separation and the remote-center neighborhood lemma.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- An endpoint occurrence position is a listed endpoint of the lifted route
owned by that syntactic endpoint. -/
theorem PlanarPresentation.contractedEndpointOccurrencePosition_mem_ownRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {endpoint : ContractedEndpoint}
    (endpointMember : endpoint ∈ problem.contractedEndpoints)
    (routeTranslate : Cell) :
    presentation.contractedEndpointOccurrencePosition
        endpoint routeTranslate ∈
      presentation.contractedEdgeRouteOccurrence
        endpoint.edge routeTranslate := by
  have endpoints :=
    presentation.contractedEdgeRouteOccurrence_normalizationEndpoints
      (endpoint.edge_mem_of_mem endpointMember) routeTranslate
  cases endpoint with
  | source edge =>
      exact List.mem_of_mem_head? endpoints.1
  | target edge =>
      exact List.mem_of_mem_getLast? endpoints.2

/-- Source-incident specialization: a different endpoint occurrence at the
same lifted source vertex selects a different port, so its template strictly
avoids the owning route's trimmed corridor. -/
theorem ContinuousPlanarPresentation.firstNormalizationCorridorOccurrence_strictlyAvoids_incidentSourceTemplate
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
      (planar.firstNormalizationCorridorOccurrence edge routeTranslate)
      (planar.firstNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute :=
    planar.contractedEdgeRouteOccurrence edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRouteOccurrence_length_ge_two
      degree edgeMember routeTranslate
  have routeSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    planar.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple edgeMember routeTranslate
  have routeOrthogonal : OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  obtain ⟨first, second, rest, routeEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  have firstEqual : first =
      planar.contractedEndpointOccurrencePosition
        sourceEndpoint routeTranslate := by
    change oldRoute.head? = _ ∧ oldRoute.getLast? = _ at endpoints
    rw [routeEquation] at endpoints
    exact Option.some.inj endpoints.1
  subst first
  rw [routeEquation] at routeSimple routeOrthogonal
  have verticesEqual : endpoint.vertex = sourceEndpoint.vertex :=
    congrArg Prod.fst sameKey
  have positionsEqual :=
    planar.contractedEndpointOccurrencePosition_eq_of_key_eq sameKey
  have endpointsDifferent : endpoint ≠ sourceEndpoint := by
    intro equal
    subst endpoint
    have translatesEqual :=
      sourceEndpoint.occurrenceKey_injective_for_endpoint sameKey
    exact differentOccurrences (Prod.ext rfl translatesEqual)
  have portsDifferent := endpoint.firstNormalizedPort_ne
    presentation wellFormed degree endpointMember sourceMember
    endpointsDifferent verticesEqual
  have sourceUsed := sourceEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree sourceMember
  have sourceDirection :
      AxisDirection.between
          (planar.contractedEndpointOccurrencePosition
            sourceEndpoint routeTranslate) second =
        (sourceEndpoint.outwardSide planar).direction := by
    calc
      _ = AxisDirection.polylineFirstDirection oldRoute := by
        rw [routeEquation]
        rfl
      _ = AxisDirection.polylineFirstDirection
          (planar.contractedEdgeRoute edge) := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = sourceEndpoint.outwardDirection planar := by
        rfl
      _ = (sourceEndpoint.outwardSide planar).direction :=
        (sourceEndpoint.outwardSide_direction
          planar degree sourceMember).symm
  have incident :=
    trimmedMagnifiedRoute_strictlyAvoids_incident_otherTemplate
      (planar.contractedEndpointOccurrencePosition
        sourceEndpoint routeTranslate)
      second rest routeSimple routeOrthogonal
      (sourceEndpoint.outwardSide planar) sourceDirection
      (omittedSideAt planar sourceEndpoint.vertex) sourceUsed
      (endpoint.firstNormalizedPort planar)
      (by
        simpa [ContractedEndpoint.firstNormalizedPort,
          verticesEqual] using portsDifferent)
  rw [← routeEquation] at incident
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute oldRoute)
    (normalizationTemplateAt
      (planar.contractedEndpointOccurrencePosition
        endpoint endpointTranslate)
      (route (omittedSideAt planar endpoint.vertex)
        (endpoint.firstNormalizedPort planar)))
  rw [positionsEqual, verticesEqual]
  exact incident

/-- Target-incident specialization, symmetric to the source result. -/
theorem ContinuousPlanarPresentation.firstNormalizationCorridorOccurrence_strictlyAvoids_incidentTargetTemplate
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
      (planar.firstNormalizationCorridorOccurrence edge routeTranslate)
      (planar.firstNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute :=
    planar.contractedEdgeRouteOccurrence edge routeTranslate
  let targetEndpoint := ContractedEndpoint.target edge
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRouteOccurrence_length_ge_two
      degree edgeMember routeTranslate
  have routeSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    planar.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple edgeMember routeTranslate
  have routeOrthogonal : OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  obtain ⟨leading, before, last, routeEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  have lastEqual : last =
      planar.contractedEndpointOccurrencePosition
        targetEndpoint routeTranslate := by
    change oldRoute.head? = _ ∧ oldRoute.getLast? = _ at endpoints
    rw [routeEquation] at endpoints
    rw [planar.contractedEndpointOccurrencePosition_target]
    apply Option.some.inj
    simpa using endpoints.2
  subst last
  rw [routeEquation] at routeSimple routeOrthogonal
  have verticesEqual : endpoint.vertex = targetEndpoint.vertex :=
    congrArg Prod.fst sameKey
  have positionsEqual :=
    planar.contractedEndpointOccurrencePosition_eq_of_key_eq sameKey
  have endpointsDifferent : endpoint ≠ targetEndpoint := by
    intro equal
    subst endpoint
    have translatesEqual :=
      targetEndpoint.occurrenceKey_injective_for_endpoint sameKey
    exact differentOccurrences (Prod.ext rfl translatesEqual)
  have portsDifferent := endpoint.firstNormalizedPort_ne
    presentation wellFormed degree endpointMember targetMember
    endpointsDifferent verticesEqual
  have targetUsed := targetEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree targetMember
  have finalAligned :
      (GridSegment.mk before
        (planar.contractedEndpointOccurrencePosition
          targetEndpoint routeTranslate)).IsAxisAligned :=
    (List.isChain_append_cons_cons.mp routeOrthogonal).2.1
  have targetDirection :
      AxisDirection.between
          (planar.contractedEndpointOccurrencePosition
            targetEndpoint routeTranslate) before =
        (targetEndpoint.outwardSide planar).direction := by
    calc
      _ = (AxisDirection.polylineLastDirection oldRoute).opposite := by
        rw [routeEquation]
        rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
          leading finalAligned]
        exact AxisDirection.between_reverse_eq_opposite
          (AxisDirection.between_isGenuine_of_axisAligned finalAligned)
      _ = (AxisDirection.polylineLastDirection
          (planar.contractedEdgeRoute edge)).opposite := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = targetEndpoint.outwardDirection planar := by
        rfl
      _ = (targetEndpoint.outwardSide planar).direction :=
        (targetEndpoint.outwardSide_direction
          planar degree targetMember).symm
  have incident :=
    trimmedMagnifiedRoute_strictlyAvoids_incident_otherTemplate_at_target
      leading before
      (planar.contractedEndpointOccurrencePosition
        targetEndpoint routeTranslate)
      routeSimple routeOrthogonal
      (targetEndpoint.outwardSide planar) targetDirection
      (omittedSideAt planar targetEndpoint.vertex) targetUsed
      (endpoint.firstNormalizedPort planar)
      (by
        simpa [ContractedEndpoint.firstNormalizedPort,
          verticesEqual] using portsDifferent)
  rw [← routeEquation] at incident
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute oldRoute)
    (normalizationTemplateAt
      (planar.contractedEndpointOccurrencePosition
        endpoint endpointTranslate)
      (route (omittedSideAt planar endpoint.vertex)
        (endpoint.firstNormalizedPort planar)))
  rw [positionsEqual, verticesEqual]
  exact incident

/-- If a template center is neither endpoint of another contracted route
occurrence, complete old-route separation makes it remote from every point
and axis-aligned segment of that occurrence. -/
theorem PlanarPresentation.firstNormalizationCorridorOccurrence_strictlyAvoids_remoteTemplate
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
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
    RoutesStrictlyAvoidEachOther
      (presentation.firstNormalizationCorridorOccurrence edge routeTranslate)
      (presentation.firstNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  let templateRoute := presentation.contractedEdgeRouteOccurrence
    endpoint.edge endpointTranslate
  let corridorRoute := presentation.contractedEdgeRouteOccurrence
    edge routeTranslate
  let position := presentation.contractedEndpointOccurrencePosition
    endpoint endpointTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  have templateEdgeMember := endpoint.edge_mem_of_mem endpointMember
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have oldAvoid : RoutesAvoidEachOther templateRoute corridorRoute :=
    presentation.contractedEdgeRouteOccurrences_avoidEachOther
      degree separated templateEdgeMember edgeMember
      endpointTranslate routeTranslate differentOccurrences
  have positionMember : position ∈ templateRoute := by
    exact presentation.contractedEndpointOccurrencePosition_mem_ownRoute
      endpointMember endpointTranslate
  have corridorEndpoints :=
    presentation.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  have oldPointsAvoid : ∀ point ∈ corridorRoute, point ≠ position := by
    intro point pointMember equal
    rcases List.mem_iff_get.mp positionMember with
      ⟨positionIndex, positionAt⟩
    rcases List.mem_iff_get.mp pointMember with
      ⟨pointIndex, pointAt⟩
    have indexedEqual :
        templateRoute.get positionIndex =
          corridorRoute.get pointIndex :=
      positionAt.trans (equal.symm.trans pointAt.symm)
    have contacts := oldAvoid.2.2.2
      positionIndex pointIndex indexedEqual
    rw [positionAt, pointAt] at contacts
    rcases contacts.2 with atHead | atLast
    · have pointAtSource : point =
          presentation.contractedEndpointOccurrencePosition
            sourceEndpoint routeTranslate :=
        Option.some.inj (atHead.symm.trans corridorEndpoints.1)
      have positionsEqual :
          presentation.contractedEndpointOccurrencePosition
              endpoint endpointTranslate =
            presentation.contractedEndpointOccurrencePosition
              sourceEndpoint routeTranslate :=
        equal.symm.trans pointAtSource
      exact sourceKeyDifferent
        (presentation.contractedEndpointOccurrencePosition_injective
          (endpoint.vertex_mem_of_mem endpointMember)
          (sourceEndpoint.vertex_mem_of_mem sourceMember)
          positionsEqual)
    · have pointAtTarget : point =
          presentation.contractedEndpointOccurrencePosition
            targetEndpoint routeTranslate :=
        Option.some.inj (atLast.symm.trans corridorEndpoints.2)
      have positionsEqual :
          presentation.contractedEndpointOccurrencePosition
              endpoint endpointTranslate =
            presentation.contractedEndpointOccurrencePosition
              targetEndpoint routeTranslate :=
        equal.symm.trans pointAtTarget
      exact targetKeyDifferent
        (presentation.contractedEndpointOccurrencePosition_injective
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
    presentation.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  have remote :=
    trimmedMagnifiedRoute_strictlyAvoids_normalizationTemplateAt_route
      corridorOrthogonal oldPointsAvoid oldSegmentsAvoid
      (omittedSideAt presentation endpoint.vertex)
      (endpoint.firstNormalizedPort presentation)
  change RoutesStrictlyAvoidEachOther
    (trimmedMagnifiedRoute corridorRoute)
    (normalizationTemplateAt position
      (route (omittedSideAt presentation endpoint.vertex)
        (endpoint.firstNormalizedPort presentation)))
  exact remote

/-- Complete template--corridor classification for distinct contracted route
occurrences. -/
theorem ContinuousPlanarPresentation.firstNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
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
      (planar.firstNormalizationCorridorOccurrence edge routeTranslate)
      (planar.firstNormalizationTemplateOccurrence
        endpoint endpointTranslate) := by
  dsimp only
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  by_cases sourceKeyEqual : endpoint.occurrenceKey endpointTranslate =
      sourceEndpoint.occurrenceKey routeTranslate
  · exact
      presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_incidentSourceTemplate
        wellFormed degree separated sourceSimple
        endpointMember edgeMember sourceKeyEqual differentOccurrences
  · by_cases targetKeyEqual : endpoint.occurrenceKey endpointTranslate =
        targetEndpoint.occurrenceKey routeTranslate
    · exact
        presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_incidentTargetTemplate
          wellFormed degree separated sourceSimple
          endpointMember edgeMember targetKeyEqual differentOccurrences
    · exact
        presentation.toPlanarPresentation
          |>.firstNormalizationCorridorOccurrence_strictlyAvoids_remoteTemplate
            degree separated endpointMember edgeMember
            differentOccurrences sourceKeyEqual targetKeyEqual

/-- The symmetric orientation used when a template is the first piece in an
assembly pairing. -/
theorem ContinuousPlanarPresentation.firstNormalizationTemplateOccurrence_strictlyAvoids_corridorOccurrence
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
      (planar.firstNormalizationTemplateOccurrence
        endpoint endpointTranslate)
      (planar.firstNormalizationCorridorOccurrence edge routeTranslate) := by
  dsimp only
  exact
    (presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
      wellFormed degree separated sourceSimple
      endpointMember edgeMember differentOccurrences).symm

end PeriodicThreeDM
end LeanTrominoes
