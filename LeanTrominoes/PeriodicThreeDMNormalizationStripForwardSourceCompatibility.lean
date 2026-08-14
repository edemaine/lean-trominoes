/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardSourceCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationStripExposedPortMatching
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationSiteMembership

/-!
# Forward-orientation compatibility at strip source endpoints
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- At every rectangular block occurrence, a contracted edge's source vertex
port is opposite to its source-adjacent strip routing-cell port. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_source_neighbor
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
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort planar
    let sourcePoint :=
      planar.finalNormalizationPosition edge.toPeriodicEdge.source
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod sourcePoint)
      (planar.stripPeriodTranslation translate)
    presentation.forwardStripDrawingOrientation values location port.side =
      !(presentation.forwardStripDrawingOrientation values
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
    planar.finalStripOrientationSite_vertex_mem vertexMember
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    planar.exists_finalNormalizationRoute_sourceTriple edge
  have routeSiteMember :
      (stripRasterLocation planar.finalNormalizationPeriod adjacentPoint,
        FinalOrientationSite.route edge sourcePoint adjacentPoint third) ∈
          planar.finalStripOrientationSites := by
    apply planar.finalStripOrientationSite_route_mem edgeMember []
      sourcePoint adjacentPoint third rest
    simpa [sourcePoint, adjacentPoint, port] using routeEquation
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod sourcePoint)
            (planar.stripPeriodTranslation translate)) port.side =
        Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod adjacentPoint)
          (planar.stripPeriodTranslation translate) := by
    rw [planar.latticeNeighbor_stripPeriodOccurrence]
    rw [axisDirectionOfSide_stripCanonicalPort_side]
  rw [neighborEq]
  have vertexValue :=
    presentation.forwardStripDrawingOrientation_periodOccurrence
      wellFormed degree horizontal sourceInside collisionFree values
      vertexSiteMember (translate := translate) port.side
  have routeValue :=
    presentation.forwardStripDrawingOrientation_periodOccurrence
      wellFormed degree horizontal sourceInside collisionFree values
      routeSiteMember (translate := translate) port.side.opposite
  have vertexValue' :
      presentation.forwardStripDrawingOrientation values
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod sourcePoint)
            (planar.stripPeriodTranslation translate)) port.side =
        (FinalOrientationSite.vertex endpoint.vertex).inward
          planar values translate port.side := by
    simpa [FinalOrientationSite.point, endpoint, ContractedEndpoint.vertex,
      sourcePoint] using vertexValue
  have routeValue' :
      presentation.forwardStripDrawingOrientation values
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod adjacentPoint)
            (planar.stripPeriodTranslation translate)) port.side.opposite =
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
