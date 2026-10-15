/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.OccurrenceSplitRingSpokeCycleSeparation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Positioned.RetainedAngularFanPositionedRoutes
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineSegmentBoxCheck
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictSeparationCheck
import Mathlib.Tactic.FinCases
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceRouteHull
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedRayHullSeparationCheck

/-!
# Direct copied-source prefixes avoid their inner Figure 7 cycles

The coordinated direct-source atlas stops at the outer endpoint of a
Figure 7 spoke.  This module checks the complementary mixed interaction:
the whole atlas-selected outer prefix is strictly contact-free from every
implication route in the inner square around the same variable center.

The certificate is finite over the 33 direct clause shapes, their literal
entries, eight occurrence slots, nine ring clauses, and two implication
sides.  A common translation then positions it at the selected retained
component origin.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- One factor-eight implication route positioned in the inner Figure 7
square around a direct atlas entry's source-variable center. -/
def retainedDirectSourceInnerCycleRouteAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    List Cell :=
  translatePolyline
    (Cell.sub
      (retainedDirectSourceFanCenterAt kind index)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline retainedTerminalFanRoutingRefinement
      (cycleRoute vertex literalIndex.val))

private def cycleSeparationCheck (first second : List Cell) : Bool :=
  segmentBoxesSeparateCheck first second || routesStrictlyAvoidEachOtherCheck first second

private theorem cycleSeparationCheck_sound (first second : List Cell)
    (checked : cycleSeparationCheck first second = true) :
    RoutesStrictlyAvoidEachOther first second := by
  simp only [cycleSeparationCheck, Bool.or_eq_true] at checked
  rcases checked with boxes | exactCheck
  · exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck first second boxes
  · exact (routesStrictlyAvoidEachOtherCheck_eq_true first second).mp exactCheck

private def innerCycleEntryCheck (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (vertex : RingVertex) (literalIndex : Fin 2) : Bool :=
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let cycle := retainedDirectSourceInnerCycleRouteAt kind index vertex literalIndex
  cycleSeparationCheck (retainedDirectSourceFanEscapeAt kind index slot).route cycle &&
    cycleSeparationCheck (retainedTerminalFanOuterLaneShiftRouteAt escapePoint terminal.1 slot) cycle &&
    cycleSeparationCheck (retainedTerminalFanOuterLocalRouteAt center terminal.1 slot) cycle &&
    retainedRayHullSeparationCheck (retainedTerminalFanOuterEscapedRemainingRay terminal)
      (Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)) cycle

private theorem innerCycleEntryCheck_sound (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (vertex : RingVertex) (literalIndex : Fin 2)
    (checked : innerCycleEntryCheck kind index slot vertex literalIndex = true) :
    RoutesStrictlyAvoidEachOther (retainedDirectSourceFanCompleteRouteAt kind index slot)
      (retainedDirectSourceInnerCycleRouteAt kind index vertex literalIndex) := by
  simp only [innerCycleEntryCheck, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨escapeCheck, laneCheck⟩, localCheck⟩, rayCheck⟩ := checked
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escape := retainedDirectSourceFanEscapeAt kind index slot
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let start := Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let ray := retainedTerminalFanOuterEscapedRemainingRay terminal
  have shifted := (cycleSeparationCheck_sound _ _ laneCheck).join_left
    (retainedRayHullSeparationCheck_sound ray start _ rayCheck)
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast? escapePoint terminal.1 slot)
    (ray.rasterize_head? start)
  have radial := (cycleSeparationCheck_sound _ _ escapeCheck).join_left shifted
    escape.last_eq (retainedTerminalFanOuterEscapedShiftedTail_head? center terminal slot)
  exact radial.join_left (cycleSeparationCheck_sound _ _ localCheck)
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast? center terminal slot escape
      (retainedDirectSourceFanTerminalAt_length_positive kind index)
      (retainedDirectSourceFanTerminalAt_escape_fits kind index))
    (retainedTerminalFanOuterLocalRouteAt_head? center terminal.1 slot)

private def innerCycleCheck (kind : RetainedDirectClauseKind) : Bool :=
  finiteAll fun index : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun slot : RetainedTerminalSlot =>
      cycleVertices.all fun vertex =>
        finiteAll fun literalIndex : Fin 2 =>
          innerCycleEntryCheck kind index slot vertex literalIndex

private theorem innerCycleCheck_correct_case0 :
    innerCycleCheck (.crossover 0) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case1 :
    innerCycleCheck (.crossover 1) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case2 :
    innerCycleCheck (.crossover 2) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case3 :
    innerCycleCheck (.crossover 3) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case4 :
    innerCycleCheck (.crossover 4) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case5 :
    innerCycleCheck (.crossover 5) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case6 :
    innerCycleCheck (.crossover 6) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case7 :
    innerCycleCheck (.crossover 7) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case8 :
    innerCycleCheck (.crossover 8) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case9 :
    innerCycleCheck (.crossover 9) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case10 :
    innerCycleCheck (.crossover 10) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case11 :
    innerCycleCheck (.crossover 11) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case12 :
    innerCycleCheck (.crossover 12) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case13 :
    innerCycleCheck (.crossover 13) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case14 :
    innerCycleCheck (.crossover 14) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case15 :
    innerCycleCheck (.crossover 15) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case16 :
    innerCycleCheck (.crossover 16) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case17 :
    innerCycleCheck (.crossover 17) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case18 :
    innerCycleCheck (.crossover 18) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case19 :
    innerCycleCheck (.crossover 19) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case20 :
    innerCycleCheck (.crossover 20) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case21 :
    innerCycleCheck (.crossover 21) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case22 :
    innerCycleCheck (.crossover 22) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case23 :
    innerCycleCheck (.crossover 23) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case24 :
    innerCycleCheck (.crossover 24) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case25 :
    innerCycleCheck (.crossover 25) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case26 :
    innerCycleCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case27 :
    innerCycleCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case28 :
    innerCycleCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case29 :
    innerCycleCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case30 :
    innerCycleCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case31 :
    innerCycleCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem innerCycleCheck_correct_case32 :
    innerCycleCheck .routedClause = true := by
  decide +kernel

private theorem innerCycleCheck_correct (kind : RetainedDirectClauseKind) :
    innerCycleCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact innerCycleCheck_correct_case0
    · exact innerCycleCheck_correct_case1
    · exact innerCycleCheck_correct_case2
    · exact innerCycleCheck_correct_case3
    · exact innerCycleCheck_correct_case4
    · exact innerCycleCheck_correct_case5
    · exact innerCycleCheck_correct_case6
    · exact innerCycleCheck_correct_case7
    · exact innerCycleCheck_correct_case8
    · exact innerCycleCheck_correct_case9
    · exact innerCycleCheck_correct_case10
    · exact innerCycleCheck_correct_case11
    · exact innerCycleCheck_correct_case12
    · exact innerCycleCheck_correct_case13
    · exact innerCycleCheck_correct_case14
    · exact innerCycleCheck_correct_case15
    · exact innerCycleCheck_correct_case16
    · exact innerCycleCheck_correct_case17
    · exact innerCycleCheck_correct_case18
    · exact innerCycleCheck_correct_case19
    · exact innerCycleCheck_correct_case20
    · exact innerCycleCheck_correct_case21
    · exact innerCycleCheck_correct_case22
    · exact innerCycleCheck_correct_case23
    · exact innerCycleCheck_correct_case24
    · exact innerCycleCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact innerCycleCheck_correct_case26
      · exact innerCycleCheck_correct_case27
    | middle =>
      fin_cases index
      · exact innerCycleCheck_correct_case28
      · exact innerCycleCheck_correct_case29
    | right =>
      fin_cases index
      · exact innerCycleCheck_correct_case30
      · exact innerCycleCheck_correct_case31
  | routedClause => exact innerCycleCheck_correct_case32

/-- Every coordinated direct-source outer prefix is strictly contact-free
from every implication route in its own inner Figure 7 square. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoids_innerCycleRoute :
    ∀ (vertex : RingVertex)
      (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (literalIndex : Fin 2),
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          kind index slot)
        (retainedDirectSourceInnerCycleRouteAt
          kind index vertex literalIndex) := by
  intro vertex kind index slot literalIndex
  have checked := innerCycleCheck_correct kind
  simp only [innerCycleCheck, finiteAll_eq_true, List.all_eq_true] at checked
  have member : vertex ∈ cycleVertices := by
    cases vertex with
    | separator => simp [cycleVertices]
    | port port => cases port <;> simp [cycleVertices]
  exact innerCycleEntryCheck_sound kind index slot vertex literalIndex
    (checked index slot vertex member literalIndex)

/-- Positioning a checked direct-source choice preserves its strict
separation from the correspondingly positioned inner cycle route. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_innerCycleRoute
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute slot)
      (translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceInnerCycleRouteAt
          choice.kind choice.index vertex literalIndex)) := by
  exact
    RoutesStrictlyAvoidEachOther.map_add
      (retainedDirectSourceFanCompleteRouteAt_strictlyAvoids_innerCycleRoute
        vertex choice.kind choice.index slot literalIndex)
      (retainedDirectSourceFanPositioningOffset choice.origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
