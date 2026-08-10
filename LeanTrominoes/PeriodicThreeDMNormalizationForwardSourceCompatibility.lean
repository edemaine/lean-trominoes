import LeanTrominoes.PeriodicThreeDMNormalizationOrientationOccurrence

/-!
# Forward-orientation compatibility at contracted-edge sources

The semantic value selected at a normalized source-vertex port is the source
inward value of its contracted edge.  The first routing cell stores its
negation on the side facing that vertex.  This module proves that these are
exactly the two values read by the plane-wide forward orientation at every
period occurrence.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A route site points outward toward its predecessor with the negation of
the owning edge's source value. -/
theorem routeSiteInward_toward_before
    (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (before current after translate : Cell) :
    routeSiteInward values edge before current after translate
        (Side.ofAxisDirection (AxisDirection.between current before)) =
      !(edge.sourceInward values translate) := by
  simp [routeSiteInward]

/-- The geometric side of the first routing cell that faces its source is
the opposite of the source endpoint's normalized vertex port. -/
theorem PlanarPresentation.sourceAdjacent_backwardSide
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge)
    (firstStep : AxisDirection.IsUnitAxisStep
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
      (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        ((ContractedEndpoint.source edge).finalNormalizedPort
          presentation).direction.step)) :
    Side.ofAxisDirection
        (AxisDirection.between
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)) =
      ((ContractedEndpoint.source edge).finalNormalizedPort
        presentation).side.opposite := by
  let port :=
    (ContractedEndpoint.source edge).finalNormalizedPort presentation
  have forward :
      AxisDirection.between
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            port.direction.step) =
        port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have backward :
      AxisDirection.between
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            port.direction.step)
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source) =
        port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [forward]
  rw [backward]
  rw [Side.ofAxisDirection_opposite
    (CanonicalVertexPort.direction_isGenuine port)]
  simp [port]

/-- At every lifted occurrence, a contracted edge's source-vertex port has
the value opposite to the source-adjacent routing-cell port. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_source_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort planar
    let sourcePoint :=
      planar.finalNormalizationPosition edge.toPeriodicEdge.source
    let location := reflectedLocation
      (Cell.add sourcePoint
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
    presentation.forwardDrawingOrientation values location port.side =
      !(presentation.forwardDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location port.side)
        port.side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let endpoint := ContractedEndpoint.source edge
  let port := endpoint.finalNormalizedPort planar
  let sourcePoint :=
    planar.finalNormalizationPosition edge.toPeriodicEdge.source
  let adjacentPoint := Cell.add sourcePoint port.direction.step
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp [endpoint, contractedEndpoints, edgeMember]
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have vertexSiteMember :=
    planar.finalOrientationSite_vertex_mem vertexMember
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    planar.exists_finalNormalizationRoute_sourceTriple edge
  have routeSiteMember :
      (rasterLocation planar.finalNormalizationPeriod adjacentPoint,
        FinalOrientationSite.route edge sourcePoint adjacentPoint third) ∈
          planar.finalOrientationSites := by
    apply planar.finalOrientationSite_route_mem edgeMember []
      sourcePoint adjacentPoint third rest
    simpa [sourcePoint, adjacentPoint, port] using routeEquation
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor
          (reflectedLocation
            (Cell.add sourcePoint
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          port.side =
        reflectedLocation
          (Cell.add adjacentPoint
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)) := by
    simpa [adjacentPoint] using
      latticeNeighbor_reflected_periodOccurrence
        planar.finalNormalizationPeriod sourcePoint translate port.side
  rw [neighborEq]
  have vertexValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values vertexSiteMember translate port.side
  have routeValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values routeSiteMember translate port.side.opposite
  have vertexValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add sourcePoint
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          port.side =
        (FinalOrientationSite.vertex endpoint.vertex).inward
          planar values translate port.side := by
    simpa [FinalOrientationSite.point, endpoint, ContractedEndpoint.vertex,
      sourcePoint] using vertexValue
  have routeValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add adjacentPoint
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          port.side.opposite =
        (FinalOrientationSite.route edge sourcePoint adjacentPoint third).inward
          planar values translate port.side.opposite := by
    simpa [FinalOrientationSite.point] using routeValue
  rw [vertexValue', routeValue']
  simp only [FinalOrientationSite.inward]
  have endpointValue := PlanarPresentation.vertexPortInward_endpoint
    presentation wellFormed degree values endpointMember translate
  change planar.vertexPortInward values endpoint.vertex translate port.side =
    !routeSiteInward values edge sourcePoint adjacentPoint third translate
      port.side.opposite
  have endpointValue' :
      planar.vertexPortInward values endpoint.vertex translate port.side =
        endpoint.inwardAtVertexTranslate values translate := by
    simpa [endpoint, port, ContractedEndpoint.vertex] using endpointValue
  rw [endpointValue']
  have backwardSide := planar.sourceAdjacent_backwardSide edge firstStep
  change edge.sourceInward values translate =
    !routeSiteInward values edge sourcePoint adjacentPoint third translate
      port.side.opposite
  rw [← backwardSide]
  rw [routeSiteInward_toward_before]
  cases edge.sourceInward values translate <;> rfl

end PeriodicThreeDM

end LeanTrominoes
