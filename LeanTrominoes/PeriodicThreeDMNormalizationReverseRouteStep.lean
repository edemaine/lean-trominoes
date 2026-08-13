/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReverseOrientation

/-!
# Reverse orientation transport through one normalized route cell

For an arbitrary valid orientation of the compiled drawing, the neighbor law
flips the value on entering a routing cell and the wire-or-bend constraint
flips it again on leaving.  Thus the forward-facing value is preserved across
each displayed three-point route window.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- A nonblank routing cell imposes inequality on the two sides used to
construct it. -/
theorem routingCellType_satisfiesOrientation_iff_ne
    (first second : Side) (color : WireColor) (inward : Side → Bool)
    (different : first ≠ second) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
        (routingCellType first second color) inward ↔
      inward first ≠ inward second := by
  cases first <;> cases second <;>
    simp_all [routingCellType,
      PeriodicOrthogonalDrawing.satisfiesOrientation, eq_comm]

/-- At a well-behaved internal route point, local validity says precisely
that the values facing its predecessor and successor differ. -/
theorem routingCellTypeAt_satisfiesOrientation_iff_ne
    {before current after : Cell}
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (color : WireColor) (inward : Side → Bool) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
        (routingCellTypeAt before current after color) inward ↔
      inward
          (Side.ofAxisDirection (AxisDirection.between current before)) ≠
        inward
          (Side.ofAxisDirection (AxisDirection.between current after)) := by
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
  have differentDirections :
      AxisDirection.between current before ≠
        AxisDirection.between current after := by
    rw [backward]
    exact Ne.symm noReverse
  have differentSides :
      Side.ofAxisDirection (AxisDirection.between current before) ≠
        Side.ofAxisDirection (AxisDirection.between current after) :=
    Side.ofAxisDirection_injective_of_genuine
      backwardGenuine outgoingGenuine differentDirections
  exact routingCellType_satisfiesOrientation_iff_ne _ _ color inward
    differentSides

/-- Entering and leaving one internal normalized route cell preserves the
forward-facing drawing value. -/
theorem ContinuousPlanarPresentation.drawingOrientation_routeWindow_forward_eq_predecessor
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
    let planar := presentation.toPlanarPresentation
    let predecessorSide :=
      Side.ofAxisDirection (AxisDirection.between before current)
    let forwardSide :=
      Side.ofAxisDirection (AxisDirection.between current after)
    let predecessorLocation := reflectedLocation
      (Cell.add before
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
    let currentLocation := reflectedLocation
      (Cell.add current
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
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
  let predecessorLocation := reflectedLocation
    (Cell.add before
      (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
  let currentLocation := reflectedLocation
    (Cell.add current
      (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
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
      (rasterLocation planar.finalNormalizationPeriod current,
        FinalOrientationSite.route edge before current after) ∈
          planar.finalOrientationSites := by
    exact planar.finalOrientationSite_route_mem edgeMember leading
      before current after rest routeEquation
  have lookup := planar.finalOrientationSiteAt_reflected_periodOccurrence
    collisionFree siteMember (translate := translate)
  have cellType :=
    planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree lookup
  have cellType' :
      planar.normalizedOrthogonalDrawing.getAt currentLocation =
        routingCellTypeAt before current after edge.color := by
    simpa [currentLocation, FinalOrientationSite.cellType,
      FinalOrientationSite.point] using cellType
  have localConstraint := valid.1 currentLocation
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
      ((planar.normalizedOrthogonalDrawing.getAt currentLocation).portColor
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
    rw [latticeNeighbor_reflected_periodOccurrence]
    rw [← beforePoint]
  have neighborCompatibility := valid.2 currentLocation backwardSide
    backwardExposed
  rw [neighborEq, backwardSideEq] at neighborCompatibility
  simp only [Side.opposite_opposite] at neighborCompatibility
  cases backwardValue : orientation currentLocation backwardSide <;>
    cases forwardValue : orientation currentLocation forwardSide <;>
    cases predecessorValue :
        orientation predecessorLocation predecessorSide <;>
    simp_all

end PeriodicThreeDM

end LeanTrominoes
