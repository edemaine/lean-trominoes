/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseRouteValue
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardTargetCompatibility

/-!
# Reverse strip-orientation values at route endpoints
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048
set_option linter.constructorNameAsVariable false

/-- The value on the first edge of a normalized strip route is the value read
at its source contracted endpoint. -/
theorem PlanarPresentation.stripDrawingRouteValue_source
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    (edge : ContractedEdge) (translate : Cell) :
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort presentation
    let source := presentation.finalNormalizationPosition
      edge.toPeriodicEdge.source
    let adjacent := Cell.add source port.direction.step
    presentation.stripDrawingRouteValue orientation source adjacent translate =
      presentation.stripDrawingEndpointInward orientation endpoint translate := by
  dsimp only
  let endpoint := ContractedEndpoint.source edge
  let port := endpoint.finalNormalizedPort presentation
  let source := presentation.finalNormalizationPosition
    edge.toPeriodicEdge.source
  let adjacent := Cell.add source port.direction.step
  have direction : AxisDirection.between source adjacent = port.direction := by
    exact AxisDirection.between_add_step source
      (CanonicalVertexPort.direction_isGenuine port)
  simp only [PlanarPresentation.stripDrawingRouteValue,
    PlanarPresentation.stripDrawingEndpointInward,
    PlanarPresentation.stripEndpointDrawingLocation]
  rw [show endpoint.vertex = edge.toPeriodicEdge.source by rfl]
  rw [direction]
  rw [side_ofAxisDirection_canonical]

/-- At the final edge of a strip route, the forward value is the complement
of the inward value at the translated target endpoint. -/
theorem ContinuousPlanarPresentation.stripDrawingRouteValue_target_eq_not_endpoint
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
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let endpoint := ContractedEndpoint.target edge
    let port := endpoint.finalNormalizedPort planar
    let target := normalizeVertexPosition (planar.normalizationTarget2 edge)
    let adjacent := Cell.add target port.direction.step
    let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
    planar.stripDrawingRouteValue orientation adjacent target sourceTranslate =
      !(planar.stripDrawingEndpointInward orientation endpoint
        targetTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let endpoint := ContractedEndpoint.target edge
  let port := endpoint.finalNormalizedPort planar
  let target := normalizeVertexPosition (planar.normalizationTarget2 edge)
  let adjacent := Cell.add target port.direction.step
  let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
  let targetLocation :=
    planar.stripEndpointDrawingLocation endpoint targetTranslate
  let adjacentLocation := Cell.add
    (stripReflectedLocation planar.finalNormalizationPeriod adjacent)
    (planar.stripPeriodTranslation sourceTranslate)
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp [endpoint, contractedEndpoints, edgeMember]
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have siteMember := planar.finalStripOrientationSite_vertex_mem vertexMember
  have siteLookup := presentation.finalStripOrientationSiteAt_periodOccurrence
    wellFormed degree horizontal sourceInside collisionFree siteMember
      (translate := targetTranslate)
  have endpointCellType :=
    planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree siteLookup
  have endpointCellType' :
      planar.stripNormalizedOrthogonalDrawing.getAt targetLocation =
        planar.finalVertexCellType endpoint.vertex := by
    simpa [targetLocation, PlanarPresentation.stripEndpointDrawingLocation,
      FinalOrientationSite.cellType, FinalOrientationSite.point] using
        endpointCellType
  have endpointExposed :
      ((planar.stripNormalizedOrthogonalDrawing.getAt targetLocation).portColor
        port.side).isSome := by
    rw [endpointCellType']
    have endpointColor :=
      PlanarPresentation.finalVertexCellType_portColor_endpoint
        (presentation := presentation) wellFormed degree endpointMember
    simpa [port] using congrArg Option.isSome endpointColor
  have occurrenceEquation :=
    planar.finalTargetOccurrence_add_stripPeriodTranslation
      horizontal edgeMember sourceTranslate
  have targetLocationEq :
      targetLocation =
        Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod target)
          (planar.stripPeriodTranslation sourceTranslate) := by
    simpa [targetLocation, PlanarPresentation.stripEndpointDrawingLocation,
      endpoint, ContractedEndpoint.vertex, target, targetTranslate] using
        occurrenceEquation.symm
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor targetLocation port.side =
        adjacentLocation := by
    rw [targetLocationEq]
    rw [planar.latticeNeighbor_stripPeriodOccurrence]
    simp [adjacentLocation, adjacent]
  rcases PeriodicOrthogonalDrawing.IsOrientation.neighborCompatibility
      (drawing := planar.stripNormalizedOrthogonalDrawing)
      (orientation := orientation) valid targetLocation port.side with
    ⟨neighborLaw⟩
  have neighborCompatibility := neighborLaw endpointExposed
  rw [neighborEq] at neighborCompatibility
  obtain ⟨third, reverseRest, reverseEquation, firstStep, secondStep,
      reverseNoReverse⟩ :=
    planar.exists_finalNormalizationRoute_targetTriple edge
  have forwardSide := planar.targetAdjacent_forwardSide edge firstStep
  change orientation adjacentLocation
      (Side.ofAxisDirection (AxisDirection.between adjacent target)) =
    !(orientation targetLocation port.side)
  rw [forwardSide]
  cases endpointValue : orientation targetLocation port.side <;>
    cases adjacentValue : orientation adjacentLocation port.side.opposite <;>
    simp_all

end PeriodicThreeDM

end LeanTrominoes
