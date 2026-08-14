/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardVertexCompatibility

/-!
# Forward-orientation compatibility at arbitrary strip route ports

An exposed route port points toward either the predecessor or successor in its
displayed route.  Those directions reduce to a source boundary, an internal
route window, or a target boundary.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Boolean complement compatibility is symmetric. -/
theorem strip_bool_complement_symm {first second : Bool}
    (compatible : first = !second) : second = !first := by
  cases first <;> cases second <;> simp_all

/-- Every exposed port of every explicit normalized strip route occurrence is
compatible with its drawing-lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_route_neighbor
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
    (valid : problem.IsSuppressedOrientation values)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest)
    (translate : Cell) (side : Side) (color : WireColor)
    (exposed :
      (routingCellTypeAt before current after edge.color).portColor side =
        some color) :
    let planar := presentation.toPlanarPresentation
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod current)
      (planar.stripPeriodTranslation translate)
    presentation.forwardStripDrawingOrientation values location side =
      !(presentation.forwardStripDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
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
  have outgoing :=
    (List.isChain_cons_cons.mp
      (List.isChain_cons_cons.mp suffixUnitSteps).2).1
  have suffixNoReversal :
      AxisDirection.HasNoImmediateReversal
        (before :: current :: after :: rest) := by
    rw [routeEquation] at noReversal
    simpa using hasNoImmediateReversal_drop noReversal leading.length
  have currentNoReverse := suffixNoReversal.1
  have classified := routingCellTypeAt_portColor_eq_some_classify
    incoming outgoing currentNoReverse edge.color color side exposed
  rcases classified.2 with towardBefore | towardAfter
  · rcases leading.eq_nil_or_concat' with leadingNil |
      ⟨priorLeading, previous, leadingEq⟩
    · subst leading
      have sourceHead := planar.finalNormalizationRoute_head? edge
      have sourceNext := planar.finalNormalizationRoute_tail_head? edge
      rw [routeEquation] at sourceHead sourceNext
      simp only [List.nil_append, List.head?_cons, List.tail_cons,
        Option.some.injEq] at sourceHead sourceNext
      let port :=
        (ContractedEndpoint.source edge).finalNormalizedPort planar
      have sideAtSource : side = port.side.opposite := by
        rw [towardBefore, sourceHead, sourceNext]
        have forward :
            AxisDirection.between
                (planar.finalNormalizationPosition edge.toPeriodicEdge.source)
                (Cell.add
                  (planar.finalNormalizationPosition edge.toPeriodicEdge.source)
                  port.direction.step) =
              port.direction :=
          AxisDirection.between_add_step _
            (CanonicalVertexPort.direction_isGenuine port)
        have backward :
            AxisDirection.between
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
      let sourcePoint :=
        planar.finalNormalizationPosition edge.toPeriodicEdge.source
      let sourceLocation := Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod sourcePoint)
        (planar.stripPeriodTranslation translate)
      let currentLocation := Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod current)
        (planar.stripPeriodTranslation translate)
      have sourceNeighborEq :
          PeriodicOrthogonalDrawing.latticeNeighbor sourceLocation port.side =
            currentLocation := by
        simpa [sourceLocation, currentLocation, sourcePoint, sourceNext] using
          planar.latticeNeighbor_stripPeriodOccurrence
            sourcePoint translate port.side
      have compatibility :=
        presentation.forwardStripDrawingOrientation_source_neighbor
          wellFormed degree horizontal sourceInside collisionFree values
            (edge := edge) edgeMember translate
      dsimp only at compatibility
      rw [sourceNeighborEq] at compatibility
      have reverseCompatibility := strip_bool_complement_symm compatibility
      have currentNeighborEq :
          PeriodicOrthogonalDrawing.latticeNeighbor
              currentLocation port.side.opposite = sourceLocation := by
        rw [← sourceNeighborEq]
        exact PeriodicOrthogonalDrawing.latticeNeighbor_opposite _ _
      rw [sideAtSource]
      rw [currentNeighborEq]
      simpa [currentLocation, sourceLocation] using reverseCompatibility
    · subst leading
      have routeEquation' :
          planar.finalNormalizationRoute edge =
            priorLeading ++ previous :: before :: current :: after :: rest := by
        simpa using routeEquation
      let forwardSide :=
        Side.ofAxisDirection (AxisDirection.between before current)
      have sideAtPrevious : side = forwardSide.opposite := by
        rw [towardBefore]
        have forwardGenuine :=
          AxisDirection.between_isGenuine_of_unitAxisStep incoming
        rw [AxisDirection.between_reverse_eq_opposite forwardGenuine]
        exact Side.ofAxisDirection_opposite forwardGenuine
      have compatibility :=
        presentation.forwardStripDrawingOrientation_routeWindow_neighbor
          wellFormed degree horizontal sourceInside collisionFree values
            edgeMember priorLeading previous before current after rest
              routeEquation' translate
      dsimp only at compatibility
      let previousLocation := Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod before)
        (planar.stripPeriodTranslation translate)
      let currentLocation := Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod current)
        (planar.stripPeriodTranslation translate)
      have previousNeighborEq :
          PeriodicOrthogonalDrawing.latticeNeighbor
              previousLocation forwardSide = currentLocation := by
        have currentPoint :
            current = Cell.add before (axisDirectionOfSide forwardSide).step := by
          apply route_successor_eq_add_side_step incoming
          rfl
        unfold previousLocation currentLocation
        rw [planar.latticeNeighbor_stripPeriodOccurrence]
        rw [← currentPoint]
      rw [previousNeighborEq] at compatibility
      have reverseCompatibility := strip_bool_complement_symm compatibility
      have currentNeighborEq :
          PeriodicOrthogonalDrawing.latticeNeighbor
              currentLocation forwardSide.opposite = previousLocation := by
        rw [← previousNeighborEq]
        exact PeriodicOrthogonalDrawing.latticeNeighbor_opposite _ _
      rw [sideAtPrevious]
      rw [currentNeighborEq]
      simpa [currentLocation, previousLocation] using reverseCompatibility
  · cases rest with
    | nil =>
        have targetLast := planar.finalNormalizationRoute_getLast? edge
        have targetPrevious :=
          planar.finalNormalizationRoute_reverse_tail_head? edge
        rw [routeEquation] at targetLast targetPrevious
        simp at targetLast targetPrevious
        let port :=
          (ContractedEndpoint.target edge).finalNormalizedPort planar
        have sideAtTarget : side = port.side.opposite := by
          rw [towardAfter, targetLast, targetPrevious]
          have outward :
              AxisDirection.between
                  (normalizeVertexPosition (planar.normalizationTarget2 edge))
                  (Cell.add
                    (normalizeVertexPosition (planar.normalizationTarget2 edge))
                    port.direction.step) =
                port.direction :=
            AxisDirection.between_add_step _
              (CanonicalVertexPort.direction_isGenuine port)
          have inward :
              AxisDirection.between
                  (Cell.add
                    (normalizeVertexPosition (planar.normalizationTarget2 edge))
                    port.direction.step)
                  (normalizeVertexPosition (planar.normalizationTarget2 edge)) =
                port.direction.opposite := by
            rw [AxisDirection.between_reverse_eq_opposite]
            · exact congrArg AxisDirection.opposite outward
            · rw [outward]
              exact CanonicalVertexPort.direction_isGenuine port
          rw [inward]
          rw [Side.ofAxisDirection_opposite
            (CanonicalVertexPort.direction_isGenuine port)]
          simp [port]
        let targetOccurrence :=
          normalizeVertexPosition (planar.normalizationTarget2 edge)
        let targetLocation := Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod
            targetOccurrence)
          (planar.stripPeriodTranslation translate)
        let currentLocation := Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod current)
          (planar.stripPeriodTranslation translate)
        have targetNeighborEq :
            PeriodicOrthogonalDrawing.latticeNeighbor
                targetLocation port.side = currentLocation := by
          simpa [targetLocation, currentLocation, targetOccurrence,
            targetPrevious] using
            planar.latticeNeighbor_stripPeriodOccurrence
              targetOccurrence translate port.side
        have compatibility :=
          presentation.forwardStripDrawingOrientation_target_neighbor
            wellFormed degree horizontal sourceInside collisionFree values valid
              (edge := edge) edgeMember translate
        dsimp only at compatibility
        rw [targetNeighborEq] at compatibility
        have reverseCompatibility := strip_bool_complement_symm compatibility
        have currentNeighborEq :
            PeriodicOrthogonalDrawing.latticeNeighbor
                currentLocation port.side.opposite = targetLocation := by
          rw [← targetNeighborEq]
          exact PeriodicOrthogonalDrawing.latticeNeighbor_opposite _ _
        rw [sideAtTarget]
        rw [currentNeighborEq]
        simpa [currentLocation, targetLocation] using reverseCompatibility
    | cons next trailing =>
        have compatibility :=
          presentation.forwardStripDrawingOrientation_routeWindow_neighbor
            wellFormed degree horizontal sourceInside collisionFree values
              edgeMember leading before current after next trailing
                (by simpa using routeEquation) translate
        simpa [towardAfter] using compatibility

end PeriodicThreeDM

end LeanTrominoes
