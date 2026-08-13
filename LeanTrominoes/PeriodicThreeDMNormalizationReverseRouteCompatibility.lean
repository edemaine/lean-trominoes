/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReverseRouteStep
import LeanTrominoes.PeriodicThreeDMNormalizationForwardTargetCompatibility

/-!
# Reverse orientation transport across complete normalized routes

The one-cell preservation law is iterated from the source vertex to the last
routing cell.  The drawing neighbor law at the translated target then proves
that the inward values read at the two contracted endpoints are opposite.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- The oriented half-edge value at `before` pointing along a normalized
route toward its successor `after`. -/
def PlanarPresentation.drawingRouteValue
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    (before after translate : Cell) : Bool :=
  orientation
    (reflectedLocation
      (Cell.add before
        (Cell.scale (presentation.finalNormalizationPeriod : Int) translate)))
    (Side.ofAxisDirection (AxisDirection.between before after))

/-- The local route-window theorem expressed in terms of the value attached
to each directed consecutive pair. -/
theorem ContinuousPlanarPresentation.drawingRouteValue_window
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest)
    (translate : Cell) :
    presentation.toPlanarPresentation.drawingRouteValue orientation
        current after translate =
      presentation.toPlanarPresentation.drawingRouteValue orientation
        before current translate := by
  simpa [PlanarPresentation.drawingRouteValue] using
    presentation.drawingOrientation_routeWindow_forward_eq_predecessor
      wellFormed degree collisionFree orientation valid edgeMember leading
        before current after rest routeEquation translate

/-- Two presentations of a list as a prefix followed by a final pair have
the same final pair. -/
theorem List.lastPair_eq_of_append_pair_eq
    {α : Type*} (firstPrefix secondPrefix : List α)
    (first second third fourth : α)
    (equal :
      firstPrefix ++ [first, second] = secondPrefix ++ [third, fourth]) :
    first = third ∧ second = fourth := by
  have reverseEqual := congrArg List.reverse equal
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append] at reverseEqual
  injection reverseEqual with secondEqual tailsEqual
  injection tailsEqual with firstEqual
  exact ⟨firstEqual, secondEqual⟩

/-- Iterating the route-window law from an arbitrary displayed pair reaches
the fixed final pair of the same route. -/
private theorem ContinuousPlanarPresentation.drawingRouteValue_eq_finalAux
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (targetLeading : List Cell) (targetBefore target : Cell)
    (targetEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        targetLeading ++ [targetBefore, target])
    (translate : Cell) :
    ∀ (rest : List Cell) (leading : List Cell)
      (before current after : Cell),
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest →
      presentation.toPlanarPresentation.drawingRouteValue orientation
          before current translate =
        presentation.toPlanarPresentation.drawingRouteValue orientation
          targetBefore target translate := by
  intro rest
  induction rest with
  | nil =>
      intro leading before current after routeEquation
      have finalPairs : current = targetBefore ∧ after = target := by
        apply List.lastPair_eq_of_append_pair_eq
          (leading ++ [before]) targetLeading current after
            targetBefore target
        calc
          (leading ++ [before]) ++ [current, after] =
              leading ++ before :: current :: after :: [] := by simp
          _ = presentation.toPlanarPresentation.finalNormalizationRoute edge :=
            routeEquation.symm
          _ = targetLeading ++ [targetBefore, target] := targetEquation
      have window := presentation.drawingRouteValue_window
        wellFormed degree collisionFree orientation valid edgeMember leading
          before current after [] routeEquation translate
      calc
        presentation.toPlanarPresentation.drawingRouteValue orientation
            before current translate =
            presentation.toPlanarPresentation.drawingRouteValue orientation
              current after translate := window.symm
        _ = presentation.toPlanarPresentation.drawingRouteValue orientation
              targetBefore target translate := by
          rw [finalPairs.1, finalPairs.2]
  | cons next tail induction =>
      intro leading before current after routeEquation
      have window := presentation.drawingRouteValue_window
        wellFormed degree collisionFree orientation valid edgeMember leading
          before current after (next :: tail) routeEquation translate
      have nextEquation :
          presentation.toPlanarPresentation.finalNormalizationRoute edge =
            (leading ++ [before]) ++
              current :: after :: next :: tail := by
        rw [routeEquation]
        simp
      exact window.symm.trans
        (induction (leading ++ [before]) current after next nextEquation)

/-- The value on the first edge of a final normalized route is the value read
at its source contracted endpoint. -/
theorem PlanarPresentation.drawingRouteValue_source
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    (edge : ContractedEdge) (translate : Cell) :
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort presentation
    let source := presentation.finalNormalizationPosition
      edge.toPeriodicEdge.source
    let adjacent := Cell.add source port.direction.step
    presentation.drawingRouteValue orientation source adjacent translate =
      presentation.drawingEndpointInward orientation endpoint translate := by
  dsimp only
  let endpoint := ContractedEndpoint.source edge
  let port := endpoint.finalNormalizedPort presentation
  let source := presentation.finalNormalizationPosition
    edge.toPeriodicEdge.source
  let adjacent := Cell.add source port.direction.step
  have direction : AxisDirection.between source adjacent = port.direction := by
    exact AxisDirection.between_add_step source
      (CanonicalVertexPort.direction_isGenuine port)
  simp only [PlanarPresentation.drawingRouteValue,
    PlanarPresentation.drawingEndpointInward,
    PlanarPresentation.endpointDrawingLocation]
  rw [show endpoint.vertex = edge.toPeriodicEdge.source by rfl]
  rw [direction]
  rw [side_ofAxisDirection_canonical]

/-- At the final edge of a route, the forward value is the complement of the
inward value at the translated target endpoint. -/
theorem ContinuousPlanarPresentation.drawingRouteValue_target_eq_not_endpoint
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let endpoint := ContractedEndpoint.target edge
    let port := endpoint.finalNormalizedPort planar
    let target := normalizeVertexPosition (planar.normalizationTarget2 edge)
    let adjacent := Cell.add target port.direction.step
    let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
    planar.drawingRouteValue orientation adjacent target sourceTranslate =
      !(planar.drawingEndpointInward orientation endpoint targetTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let endpoint := ContractedEndpoint.target edge
  let port := endpoint.finalNormalizedPort planar
  let target := normalizeVertexPosition (planar.normalizationTarget2 edge)
  let adjacent := Cell.add target port.direction.step
  let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
  let targetLocation := planar.endpointDrawingLocation endpoint targetTranslate
  let adjacentLocation := reflectedLocation
    (Cell.add adjacent
      (Cell.scale (planar.finalNormalizationPeriod : Int) sourceTranslate))
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp [endpoint, contractedEndpoints, edgeMember]
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have siteMember := planar.finalOrientationSite_vertex_mem vertexMember
  have siteLookup := planar.finalOrientationSiteAt_reflected_periodOccurrence
    collisionFree siteMember (translate := targetTranslate)
  have endpointCellType :=
    planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree siteLookup
  have endpointCellType' :
      planar.normalizedOrthogonalDrawing.getAt targetLocation =
        planar.finalVertexCellType endpoint.vertex := by
    simpa [targetLocation, PlanarPresentation.endpointDrawingLocation,
      FinalOrientationSite.cellType, FinalOrientationSite.point] using
        endpointCellType
  have endpointExposed :
      ((planar.normalizedOrthogonalDrawing.getAt targetLocation).portColor
        port.side).isSome := by
    rw [endpointCellType']
    have endpointColor :=
      PlanarPresentation.finalVertexCellType_portColor_endpoint
        (presentation := presentation) wellFormed degree endpointMember
    simpa [port] using congrArg Option.isSome endpointColor
  have occurrenceEquation :=
    planar.finalTargetOccurrence_add_periodTranslation edge sourceTranslate
  have targetLocationEq :
      targetLocation =
        reflectedLocation
          (Cell.add target
            (Cell.scale (planar.finalNormalizationPeriod : Int)
              sourceTranslate)) := by
    apply congrArg reflectedLocation
    simpa [targetLocation, PlanarPresentation.endpointDrawingLocation,
      endpoint, ContractedEndpoint.vertex, target, targetTranslate] using
        occurrenceEquation.symm
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor targetLocation port.side =
        adjacentLocation := by
    rw [targetLocationEq]
    rw [latticeNeighbor_reflected_periodOccurrence]
    simp [adjacentLocation, adjacent]
  have neighborCompatibility := valid.2 targetLocation port.side
    endpointExposed
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

/-- Every valid drawing orientation assigns opposite inward values to the two
ends of each complete contracted route. -/
theorem ContinuousPlanarPresentation.drawingEndpointInward_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let targetTranslate := Cell.add sourceTranslate edge.toPeriodicEdge.offset
    planar.drawingEndpointInward orientation (.source edge) sourceTranslate ≠
      planar.drawingEndpointInward orientation (.target edge)
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
  have routeValues := presentation.drawingRouteValue_eq_finalAux
    wellFormed degree collisionFree orientation valid edgeMember
      (targetRest.reverse ++ [targetThird]) targetAdjacent target
        targetEquation sourceTranslate sourceRest [] source sourceAdjacent
          sourceThird sourceEquation'
  have sourceValue := planar.drawingRouteValue_source
    orientation edge sourceTranslate
  have targetValue := presentation.drawingRouteValue_target_eq_not_endpoint
    wellFormed degree collisionFree orientation valid edgeMember sourceTranslate
  change planar.drawingEndpointInward orientation sourceEndpoint
      sourceTranslate ≠
    planar.drawingEndpointInward orientation targetEndpoint targetTranslate
  have sourceValue' :
      planar.drawingRouteValue orientation source sourceAdjacent
          sourceTranslate =
        planar.drawingEndpointInward orientation sourceEndpoint
          sourceTranslate := by
    simpa [sourceEndpoint, sourcePort, source, sourceAdjacent] using sourceValue
  have targetValue' :
      planar.drawingRouteValue orientation targetAdjacent target
          sourceTranslate =
        !(planar.drawingEndpointInward orientation targetEndpoint
          targetTranslate) := by
    simpa [targetEndpoint, targetPort, target, targetAdjacent,
      targetTranslate] using targetValue
  rw [← sourceValue', routeValues, targetValue']
  cases planar.drawingEndpointInward orientation targetEndpoint targetTranslate <;>
    decide

end PeriodicThreeDM

end LeanTrominoes
