/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardTargetCompatibility

/-!
# Forward-orientation compatibility inside normalized routes

Two consecutive internal cells of one final normalized route use the same
source-based Boolean.  The first exposes it toward its successor, while the
second exposes its negation toward its predecessor.  This module lifts that
fact through provenance lookup at every period occurrence.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Consecutive internal cells of a final normalized route have compatible
forward-orientation values on their common port at every period translate. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_routeWindow_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current next after : Cell)
    (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: next :: after :: rest)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    let side := Side.ofAxisDirection (AxisDirection.between current next)
    let location := reflectedLocation
      (Cell.add current
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
    presentation.forwardDrawingOrientation values location side =
      !(presentation.forwardDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let side := Side.ofAxisDirection (AxisDirection.between current next)
  have unitSteps := presentation.finalNormalizationRoute_unitSteps
    wellFormed degree edgeMember
  have noReversal :=
    presentation.finalNormalizationRoute_hasNoImmediateReversal
      wellFormed degree edgeMember
  have suffixUnitSteps :
      (before :: current :: next :: after :: rest).IsChain
        AxisDirection.IsUnitAxisStep := by
    rw [routeEquation] at unitSteps
    exact (List.isChain_append.mp unitSteps).2.1
  have firstStep := (List.isChain_cons_cons.mp suffixUnitSteps).1
  have afterFirst := (List.isChain_cons_cons.mp suffixUnitSteps).2
  have middleStep := (List.isChain_cons_cons.mp afterFirst).1
  have afterMiddle := (List.isChain_cons_cons.mp afterFirst).2
  have lastStep := (List.isChain_cons_cons.mp afterMiddle).1
  have suffixNoReversal :
      AxisDirection.HasNoImmediateReversal
        (before :: current :: next :: after :: rest) := by
    rw [routeEquation] at noReversal
    simpa using hasNoImmediateReversal_drop noReversal leading.length
  have currentNoReverse := suffixNoReversal.1
  have nextNoReverse := suffixNoReversal.2.1
  have currentSiteMember :
      (rasterLocation planar.finalNormalizationPeriod current,
        FinalOrientationSite.route edge before current next) ∈
          planar.finalOrientationSites := by
    apply planar.finalOrientationSite_route_mem edgeMember leading
      before current next (after :: rest)
    simpa using routeEquation
  have nextSiteMember :
      (rasterLocation planar.finalNormalizationPeriod next,
        FinalOrientationSite.route edge current next after) ∈
          planar.finalOrientationSites := by
    apply planar.finalOrientationSite_route_mem edgeMember (leading ++ [before])
      current next after rest
    rw [routeEquation]
    simp
  have nextPoint :
      next = Cell.add current (axisDirectionOfSide side).step := by
    apply route_successor_eq_add_side_step middleStep
    rfl
  have neighborEq :
      PeriodicOrthogonalDrawing.latticeNeighbor
          (reflectedLocation
            (Cell.add current
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          side =
        reflectedLocation
          (Cell.add next
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)) := by
    rw [latticeNeighbor_reflected_periodOccurrence]
    rw [← nextPoint]
  rw [neighborEq]
  have currentValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values currentSiteMember translate side
  have nextValue :=
    presentation.forwardDrawingOrientation_periodOccurrence collisionFree
      values nextSiteMember translate side.opposite
  have currentValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add current
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          side =
        (FinalOrientationSite.route edge before current next).inward
          planar values translate side := by
    simpa [FinalOrientationSite.point] using currentValue
  have nextValue' :
      presentation.forwardDrawingOrientation values
          (reflectedLocation
            (Cell.add next
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          side.opposite =
        (FinalOrientationSite.route edge current next after).inward
          planar values translate side.opposite := by
    simpa [FinalOrientationSite.point] using nextValue
  rw [currentValue', nextValue']
  simp only [FinalOrientationSite.inward]
  have currentForward :
      routeSiteInward values edge before current next translate side =
        edge.sourceInward values translate := by
    exact routeSiteInward_toward_after values edge before current next translate
      firstStep middleStep currentNoReverse
  have middleGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep middleStep
  have nextBackwardSide :
      side.opposite =
        Side.ofAxisDirection (AxisDirection.between next current) := by
    unfold side
    rw [AxisDirection.between_reverse_eq_opposite middleGenuine]
    rw [Side.ofAxisDirection_opposite middleGenuine]
  have nextBackward :
      routeSiteInward values edge current next after translate side.opposite =
        !(edge.sourceInward values translate) := by
    rw [nextBackwardSide]
    exact routeSiteInward_toward_before
      values edge current next after translate
  rw [currentForward, nextBackward]
  cases edge.sourceInward values translate <;> rfl

end PeriodicThreeDM

end LeanTrominoes
