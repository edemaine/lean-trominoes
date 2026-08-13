/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoutePortCompleteness
import LeanTrominoes.PeriodicThreeDMNormalizationVertexSeparation

/-!
# Matching exposed ports along final normalized routes

The inverse route classifier identifies the predecessor or successor selected
by an exposed routing-cell port.  This module proves that the selected adjacent
point has the matching opposite port, using route-window matching in the
interior and the endpoint matching theorems at the two ends.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Converting a genuine geometric direction to a side and back loses no
information. -/
@[simp]
theorem axisDirectionOfSide_ofAxisDirection
    {direction : AxisDirection} (genuine : direction.IsGenuine) :
    axisDirectionOfSide (Side.ofAxisDirection direction) = direction := by
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, Side.ofAxisDirection,
      axisDirectionOfSide]

/-- The predecessor selected by a routing-cell side is the corresponding
geometric unit step from the current point. -/
theorem route_predecessor_eq_add_side_step
    {before current : Cell} {side : Side}
    (unit : AxisDirection.IsUnitAxisStep before current)
    (sideEquation :
      side = Side.ofAxisDirection (AxisDirection.between current before)) :
    before = Cell.add current (axisDirectionOfSide side).step := by
  rw [AxisDirection.add_between_step_eq_of_unitAxisStep unit.symm]
  rw [sideEquation]
  rw [axisDirectionOfSide_ofAxisDirection]
  exact AxisDirection.between_isGenuine_of_unitAxisStep unit.symm

/-- The successor selected by a routing-cell side is the corresponding
geometric unit step from the current point. -/
theorem route_successor_eq_add_side_step
    {current after : Cell} {side : Side}
    (unit : AxisDirection.IsUnitAxisStep current after)
    (sideEquation :
      side = Side.ofAxisDirection (AxisDirection.between current after)) :
    after = Cell.add current (axisDirectionOfSide side).step := by
  rw [AxisDirection.add_between_step_eq_of_unitAxisStep unit]
  rw [sideEquation]
  rw [axisDirectionOfSide_ofAxisDirection]
  exact AxisDirection.between_isGenuine_of_unitAxisStep unit

/-- Every exposed side of a displayed route triple matches the opposite side
at the geometric unit-step neighbor.  The proof covers both internal route
windows and the source/target boundary windows. -/
theorem ContinuousPlanarPresentation.finalCellTypeAt_routeTriple_port_matches
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest)
    (side : Side) (color : WireColor)
    (exposed :
      (routingCellTypeAt before current after edge.color).portColor side =
        some color) :
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        current)).portColor side =
      (presentation.toPlanarPresentation.finalCellTypeAt
        (rasterLocation
          presentation.toPlanarPresentation.finalNormalizationPeriod
          (Cell.add current (axisDirectionOfSide side).step))).portColor
            side.opposite := by
  let planar := presentation.toPlanarPresentation
  have unitSteps := presentation.finalNormalizationRoute_unitSteps
    wellFormed degree edgeMember
  have noReversal := presentation.finalNormalizationRoute_hasNoImmediateReversal
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
  have classified := routingCellTypeAt_portColor_eq_some_classify
    incoming outgoing currentNoReverse edge.color color side exposed
  rcases classified.2 with towardBefore | towardAfter
  · have beforeStep := route_predecessor_eq_add_side_step incoming towardBefore
    rw [← beforeStep]
    rcases leading.eq_nil_or_concat' with leadingNil |
      ⟨priorLeading, previous, leadingEq⟩
    · subst leading
      have sourceHead := planar.finalNormalizationRoute_head? edge
      have sourceNext := planar.finalNormalizationRoute_tail_head? edge
      rw [routeEquation] at sourceHead sourceNext
      simp only [List.nil_append, List.head?_cons, List.tail_cons,
        Option.some.injEq] at sourceHead sourceNext
      have sideAtSource :
          side =
            ((ContractedEndpoint.source edge).finalNormalizedPort planar).side.opposite := by
        rw [towardBefore, sourceHead, sourceNext]
        let port :=
          (ContractedEndpoint.source edge).finalNormalizedPort planar
        have forward : AxisDirection.between
            (planar.finalNormalizationPosition edge.toPeriodicEdge.source)
            (Cell.add
              (planar.finalNormalizationPosition edge.toPeriodicEdge.source)
              port.direction.step) = port.direction :=
          AxisDirection.between_add_step _
            (CanonicalVertexPort.direction_isGenuine port)
        have backward : AxisDirection.between
            (Cell.add
              (planar.finalNormalizationPosition edge.toPeriodicEdge.source)
              port.direction.step)
            (planar.finalNormalizationPosition edge.toPeriodicEdge.source) =
              port.direction.opposite := by
          rw [AxisDirection.between_reverse_eq_opposite]
          · exact congrArg AxisDirection.opposite forward
          · rw [forward]
            exact CanonicalVertexPort.direction_isGenuine port
        rw [backward]
        rw [Side.ofAxisDirection_opposite
          (CanonicalVertexPort.direction_isGenuine port)]
        simp [port]
      simpa [sourceHead, sourceNext, sideAtSource] using
        (PlanarPresentation.finalCellTypeAt_source_port_matches
          (presentation := presentation) wellFormed degree collisionFree
          edgeMember).symm
    · subst leading
      have routeEquation' :
          planar.finalNormalizationRoute edge =
            priorLeading ++ previous :: before :: current :: after :: rest := by
        simpa using routeEquation
      have common := presentation.finalCellTypeAt_routeWindow_port_matches
        wellFormed degree collisionFree edgeMember
        priorLeading previous before current after rest routeEquation'
      have forwardGenuine :=
        AxisDirection.between_isGenuine_of_unitAxisStep incoming
      have sideAtPrevious :
          side =
            (Side.ofAxisDirection
              (AxisDirection.between before current)).opposite := by
        rw [towardBefore]
        rw [AxisDirection.between_reverse_eq_opposite forwardGenuine]
        exact Side.ofAxisDirection_opposite forwardGenuine
      simpa [sideAtPrevious] using common.symm
  · have afterStep := route_successor_eq_add_side_step outgoing towardAfter
    rw [← afterStep]
    cases rest with
    | nil =>
        have targetLast := planar.finalNormalizationRoute_getLast? edge
        have targetPrevious :=
          planar.finalNormalizationRoute_reverse_tail_head? edge
        rw [routeEquation] at targetLast targetPrevious
        simp at targetLast targetPrevious
        have sideAtTarget :
            side =
              ((ContractedEndpoint.target edge).finalNormalizedPort planar).side.opposite := by
          rw [towardAfter, targetLast, targetPrevious]
          let port :=
            (ContractedEndpoint.target edge).finalNormalizedPort planar
          have forward : AxisDirection.between
              (normalizeVertexPosition (planar.normalizationTarget2 edge))
              (Cell.add
                (normalizeVertexPosition (planar.normalizationTarget2 edge))
                port.direction.step) = port.direction :=
            AxisDirection.between_add_step _
              (CanonicalVertexPort.direction_isGenuine port)
          have backward : AxisDirection.between
              (Cell.add
                (normalizeVertexPosition (planar.normalizationTarget2 edge))
                port.direction.step)
              (normalizeVertexPosition (planar.normalizationTarget2 edge)) =
                port.direction.opposite := by
            rw [AxisDirection.between_reverse_eq_opposite]
            · exact congrArg AxisDirection.opposite forward
            · rw [forward]
              exact CanonicalVertexPort.direction_isGenuine port
          rw [backward]
          rw [Side.ofAxisDirection_opposite
            (CanonicalVertexPort.direction_isGenuine port)]
          simp [port]
        have targetMatch :=
          PlanarPresentation.finalCellTypeAt_target_port_matches
            (presentation := presentation) wellFormed degree collisionFree
            edgeMember
        rw [← planar.rasterLocation_finalTargetOccurrence edge] at targetMatch
        simpa [targetLast, targetPrevious, sideAtTarget] using targetMatch.symm
    | cons next trailing =>
        have common := presentation.finalCellTypeAt_routeWindow_port_matches
          wellFormed degree collisionFree edgeMember
          leading before current after next trailing (by simpa using routeEquation)
        simpa [towardAfter] using common

end PeriodicThreeDM
end LeanTrominoes
