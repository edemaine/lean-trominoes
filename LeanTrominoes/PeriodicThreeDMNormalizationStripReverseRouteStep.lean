/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReverseRouteStep
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseTripleCoherence

/-!
# Reverse orientation transport through one normalized strip route cell
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048
set_option linter.constructorNameAsVariable false

/-- Entering and leaving one internal normalized strip route cell preserves
the forward-facing drawing value. -/
theorem ContinuousPlanarPresentation.stripDrawingOrientation_routeWindow_forward_eq_predecessor
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
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    let predecessorSide :=
      Side.ofAxisDirection (AxisDirection.between before current)
    let forwardSide :=
      Side.ofAxisDirection (AxisDirection.between current after)
    let predecessorLocation := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod before)
      (planar.stripPeriodTranslation translate)
    let currentLocation := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod current)
      (planar.stripPeriodTranslation translate)
    orientation currentLocation forwardSide =
      orientation predecessorLocation predecessorSide := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let predecessorSide :=
    Side.ofAxisDirection (AxisDirection.between before current)
  let backwardSide :=
    Side.ofAxisDirection (AxisDirection.between current before)
  let forwardSide :=
    Side.ofAxisDirection (AxisDirection.between current after)
  let predecessorLocation := Cell.add
    (stripReflectedLocation planar.finalNormalizationPeriod before)
    (planar.stripPeriodTranslation translate)
  let currentLocation := Cell.add
    (stripReflectedLocation planar.finalNormalizationPeriod current)
    (planar.stripPeriodTranslation translate)
  have unitSteps := presentation.finalNormalizationRoute_unitSteps
    wellFormed degree edgeMember
  have noReversal :=
    presentation.finalNormalizationRoute_hasNoImmediateReversal
      wellFormed degree edgeMember
  have suffixUnitSteps :
      (before :: current :: after :: rest).IsChain
        AxisDirection.IsUnitAxisStep := by
    rw [routeEquation] at unitSteps
    exact (List.isChain_append.mp unitSteps).2.1
  have incoming := (List.isChain_cons_cons.mp suffixUnitSteps).1
  have afterIncoming := (List.isChain_cons_cons.mp suffixUnitSteps).2
  have outgoing := (List.isChain_cons_cons.mp afterIncoming).1
  have suffixNoReversal :
      AxisDirection.HasNoImmediateReversal
        (before :: current :: after :: rest) := by
    rw [routeEquation] at noReversal
    simpa using hasNoImmediateReversal_drop noReversal leading.length
  have currentNoReverse := suffixNoReversal.1
  have siteMember :
      (stripRasterLocation planar.finalNormalizationPeriod current,
        FinalOrientationSite.route edge before current after) ∈
          planar.finalStripOrientationSites := by
    exact planar.finalStripOrientationSite_route_mem edgeMember leading
      before current after rest routeEquation
  have lookup := presentation.finalStripOrientationSiteAt_periodOccurrence
    wellFormed degree horizontal sourceInside collisionFree siteMember
      (translate := translate)
  have cellType :=
    planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree lookup
  have cellType' :
      planar.stripNormalizedOrthogonalDrawing.getAt currentLocation =
        routingCellTypeAt before current after edge.color := by
    simpa [currentLocation, FinalOrientationSite.cellType,
      FinalOrientationSite.point] using cellType
  rcases PeriodicOrthogonalDrawing.IsOrientation.localConstraint
      (drawing := planar.stripNormalizedOrthogonalDrawing)
      (orientation := orientation) valid currentLocation with
    ⟨localConstraint⟩
  rw [cellType'] at localConstraint
  have localDifferent :
      orientation currentLocation backwardSide ≠
        orientation currentLocation forwardSide := by
    exact (routingCellTypeAt_satisfiesOrientation_iff_ne
      incoming outgoing currentNoReverse edge.color
        (orientation currentLocation)).mp localConstraint
  have backwardSideEq : backwardSide = predecessorSide.opposite := by
    have incomingGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep incoming
    have reverse :
        AxisDirection.between current before =
          (AxisDirection.between before current).opposite :=
      AxisDirection.between_reverse_eq_opposite incomingGenuine
    simp only [backwardSide, predecessorSide]
    rw [reverse]
    exact Side.ofAxisDirection_opposite incomingGenuine
  have backwardExposed :
      ((planar.stripNormalizedOrthogonalDrawing.getAt currentLocation).portColor
        backwardSide).isSome := by
    rw [cellType', backwardSideEq]
    rw [routingCellTypeAt_portColor_toward_before
      incoming outgoing currentNoReverse]
    simp
  have beforePoint :
      before = Cell.add current (axisDirectionOfSide backwardSide).step := by
    apply route_successor_eq_add_side_step incoming.symm
    rfl
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor currentLocation backwardSide =
        predecessorLocation := by
    simp only [currentLocation, predecessorLocation]
    rw [planar.latticeNeighbor_stripPeriodOccurrence]
    rw [← beforePoint]
  rcases PeriodicOrthogonalDrawing.IsOrientation.neighborCompatibility
      (drawing := planar.stripNormalizedOrthogonalDrawing)
      (orientation := orientation) valid currentLocation backwardSide with
    ⟨neighborLaw⟩
  have neighborCompatibility := neighborLaw backwardExposed
  rw [neighborEq, backwardSideEq] at neighborCompatibility
  simp only [Side.opposite_opposite] at neighborCompatibility
  cases backwardValue : orientation currentLocation backwardSide <;>
    cases forwardValue : orientation currentLocation forwardSide <;>
    cases predecessorValue :
        orientation predecessorLocation predecessorSide <;>
    simp_all

end PeriodicThreeDM

end LeanTrominoes
