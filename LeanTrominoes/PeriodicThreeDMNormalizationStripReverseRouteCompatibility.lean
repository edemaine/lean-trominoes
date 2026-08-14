/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseRouteEndpoints

/-!
# Reverse orientation transport across complete normalized strip routes
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Every valid strip drawing orientation assigns opposite inward values to
the two ends of each complete contracted route. -/
theorem ContinuousPlanarPresentation.stripDrawingEndpointInward_ne
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
    let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
    planar.stripDrawingEndpointInward orientation (.source edge)
        sourceTranslate ≠
      planar.stripDrawingEndpointInward orientation (.target edge)
        targetTranslate := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let sourcePort := sourceEndpoint.finalNormalizedPort planar
  let source := planar.finalNormalizationPosition edge.toPeriodicEdge.source
  let sourceAdjacent := Cell.add source sourcePort.direction.step
  let targetEndpoint := ContractedEndpoint.target edge
  let targetPort := targetEndpoint.finalNormalizedPort planar
  let target := normalizeVertexPosition (planar.normalizationTarget2 edge)
  let targetAdjacent := Cell.add target targetPort.direction.step
  let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
  obtain ⟨sourceThird, sourceRest, sourceEquation, sourceFirstStep,
      sourceSecondStep, sourceNoReverse⟩ :=
    planar.exists_finalNormalizationRoute_sourceTriple edge
  obtain ⟨targetThird, targetRest, targetReverseEquation, targetFirstStep,
      targetSecondStep, targetNoReverse⟩ :=
    planar.exists_finalNormalizationRoute_targetTriple edge
  have targetForwardEquation := congrArg List.reverse targetReverseEquation
  simp only [List.reverse_reverse, List.reverse_cons] at targetForwardEquation
  have targetEquation :
      planar.finalNormalizationRoute edge =
        (targetRest.reverse ++ [targetThird]) ++ [targetAdjacent, target] := by
    simpa [targetAdjacent, target, targetPort] using targetForwardEquation
  have sourceEquation' :
      planar.finalNormalizationRoute edge =
        [] ++ source :: sourceAdjacent :: sourceThird :: sourceRest := by
    simpa [source, sourceAdjacent, sourcePort] using sourceEquation
  have routeValues := presentation.stripDrawingRouteValue_eq_finalAux
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      edgeMember (targetRest.reverse ++ [targetThird]) targetAdjacent target
        targetEquation sourceTranslate sourceRest [] source sourceAdjacent
          sourceThird sourceEquation'
  have sourceValue := planar.stripDrawingRouteValue_source
    orientation edge sourceTranslate
  have targetValue :=
    presentation.stripDrawingRouteValue_target_eq_not_endpoint
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        edgeMember sourceTranslate
  change planar.stripDrawingEndpointInward orientation sourceEndpoint
      sourceTranslate ≠
    planar.stripDrawingEndpointInward orientation targetEndpoint targetTranslate
  have sourceValue' :
      planar.stripDrawingRouteValue orientation source sourceAdjacent
          sourceTranslate =
        planar.stripDrawingEndpointInward orientation sourceEndpoint
          sourceTranslate := by
    simpa [sourceEndpoint, sourcePort, source, sourceAdjacent] using sourceValue
  have targetValue' :
      planar.stripDrawingRouteValue orientation targetAdjacent target
          sourceTranslate =
        !(planar.stripDrawingEndpointInward orientation targetEndpoint
          targetTranslate) := by
    simpa [targetEndpoint, targetPort, target, targetAdjacent,
      targetTranslate] using targetValue
  rw [← sourceValue', routeValues, targetValue']
  cases planar.stripDrawingEndpointInward orientation targetEndpoint
    targetTranslate <;> decide

end PeriodicThreeDM

end LeanTrominoes
