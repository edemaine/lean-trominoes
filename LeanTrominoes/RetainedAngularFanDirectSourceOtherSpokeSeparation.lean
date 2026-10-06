/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoiceSpokePairs
import LeanTrominoes.OrthogonalPolylineSegmentBoxCheck
import LeanTrominoes.RetainedRayHullSeparationCheck
import Mathlib.Tactic.FinCases

/-!
# Direct source prefixes avoid other spokes at their own center

The existing finite atlas checks prefix--spoke interactions between
different direct incidences of one clause.  Mixed direct/fallback
cross-clause separation also needs the complementary diagonal entry: the
coordinated prefix of one direct incidence must avoid a different occurrence
slot's Figure 7 spoke at the same variable center.

Both objects are finite atlas routes, so all direct clause kinds, atlas
indices, and slot pairs are checked exhaustively.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every direct atlas prefix avoids every different Figure 7 spoke at the
same local variable center. -/
def RetainedDirectClauseKind.SourceOtherFigure7SpokesSeparated
    (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (index :
      Fin (retainedDirectSourcePrefixChoices kind).length),
    ∀ firstSlot secondSlot : RetainedTerminalSlot,
      firstSlot ≠ secondSlot →
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceFanCompleteRouteAt
            kind index firstSlot)
          (retainedDirectSourceFigure7SpokeAt
            kind index secondSlot)

instance (kind : RetainedDirectClauseKind) :
    Decidable kind.SourceOtherFigure7SpokesSeparated := by
  unfold
    RetainedDirectClauseKind.SourceOtherFigure7SpokesSeparated
  letI :
      ∀ index :
        Fin (retainedDirectSourcePrefixChoices kind).length,
        Decidable
          (∀ firstSlot secondSlot : RetainedTerminalSlot,
            firstSlot ≠ secondSlot →
              RoutesStrictlyAvoidEachOther
                (retainedDirectSourceFanCompleteRouteAt
                  kind index firstSlot)
                (retainedDirectSourceFigure7SpokeAt
                  kind index secondSlot)) :=
    fun _ => inferInstance
  exact Fintype.decidableForallFintype

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private def otherSpokeShortCheck (first second : List Cell) : Bool :=
  segmentBoxesSeparateCheck first second || routesStrictlyAvoidEachOtherCheck first second

private theorem otherSpokeShortCheck_sound (first second : List Cell)
    (checked : otherSpokeShortCheck first second = true) :
    RoutesStrictlyAvoidEachOther first second := by
  simp only [otherSpokeShortCheck, Bool.or_eq_true] at checked
  rcases checked with boxes | exactCheck
  · exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck first second boxes
  · exact (routesStrictlyAvoidEachOtherCheck_eq_true first second).mp exactCheck

private def otherSpokeEntryCheck (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot secondSlot : RetainedTerminalSlot) : Bool :=
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let cycle := retainedDirectSourceFigure7SpokeAt kind index secondSlot
  otherSpokeShortCheck (retainedDirectSourceFanEscapeAt kind index slot).route cycle &&
    otherSpokeShortCheck (retainedTerminalFanOuterLaneShiftRouteAt escapePoint terminal.1 slot) cycle &&
    otherSpokeShortCheck (retainedTerminalFanOuterLocalRouteAt center terminal.1 slot) cycle &&
    retainedRayHullSeparationCheck (retainedTerminalFanOuterEscapedRemainingRay terminal)
      (Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)) cycle

private theorem otherSpokeEntryCheck_sound (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot secondSlot : RetainedTerminalSlot)
    (checked : otherSpokeEntryCheck kind index slot secondSlot = true) :
    RoutesStrictlyAvoidEachOther (retainedDirectSourceFanCompleteRouteAt kind index slot)
      (retainedDirectSourceFigure7SpokeAt kind index secondSlot) := by
  simp only [otherSpokeEntryCheck, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨escapeCheck, laneCheck⟩, localCheck⟩, rayCheck⟩ := checked
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escape := retainedDirectSourceFanEscapeAt kind index slot
  let escapePoint := retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let start := Cell.add escapePoint (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let ray := retainedTerminalFanOuterEscapedRemainingRay terminal
  have shifted := (otherSpokeShortCheck_sound _ _ laneCheck).join_left
    (retainedRayHullSeparationCheck_sound ray start _ rayCheck)
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast? escapePoint terminal.1 slot)
    (ray.rasterize_head? start)
  have radial := (otherSpokeShortCheck_sound _ _ escapeCheck).join_left shifted
    escape.last_eq (retainedTerminalFanOuterEscapedShiftedTail_head? center terminal slot)
  exact radial.join_left (otherSpokeShortCheck_sound _ _ localCheck)
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast? center terminal slot escape
      (retainedDirectSourceFanTerminalAt_length_positive kind index)
      (retainedDirectSourceFanTerminalAt_escape_fits kind index))
    (retainedTerminalFanOuterLocalRouteAt_head? center terminal.1 slot)

private def otherSpokesCheck (kind : RetainedDirectClauseKind) : Bool :=
  finiteAll fun index : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck (firstSlot ≠ secondSlot)
          (otherSpokeEntryCheck kind index firstSlot secondSlot)

private theorem otherSpokesCheck_case0 : otherSpokesCheck (.crossover 0) = true := by
  decide +kernel

private theorem otherSpokesCheck_case1 : otherSpokesCheck (.crossover 1) = true := by
  decide +kernel

private theorem otherSpokesCheck_case2 : otherSpokesCheck (.crossover 2) = true := by
  decide +kernel

private theorem otherSpokesCheck_case3 : otherSpokesCheck (.crossover 3) = true := by
  decide +kernel

private theorem otherSpokesCheck_case4 : otherSpokesCheck (.crossover 4) = true := by
  decide +kernel

private theorem otherSpokesCheck_case5 : otherSpokesCheck (.crossover 5) = true := by
  decide +kernel

private theorem otherSpokesCheck_case6 : otherSpokesCheck (.crossover 6) = true := by
  decide +kernel

private theorem otherSpokesCheck_case7 : otherSpokesCheck (.crossover 7) = true := by
  decide +kernel

private theorem otherSpokesCheck_case8 : otherSpokesCheck (.crossover 8) = true := by
  decide +kernel

private theorem otherSpokesCheck_case9 : otherSpokesCheck (.crossover 9) = true := by
  decide +kernel

private theorem otherSpokesCheck_case10 : otherSpokesCheck (.crossover 10) = true := by
  decide +kernel

private theorem otherSpokesCheck_case11 : otherSpokesCheck (.crossover 11) = true := by
  decide +kernel

private theorem otherSpokesCheck_case12 : otherSpokesCheck (.crossover 12) = true := by
  decide +kernel

private theorem otherSpokesCheck_case13 : otherSpokesCheck (.crossover 13) = true := by
  decide +kernel

private theorem otherSpokesCheck_case14 : otherSpokesCheck (.crossover 14) = true := by
  decide +kernel

private theorem otherSpokesCheck_case15 : otherSpokesCheck (.crossover 15) = true := by
  decide +kernel

private theorem otherSpokesCheck_case16 : otherSpokesCheck (.crossover 16) = true := by
  decide +kernel

private theorem otherSpokesCheck_case17 : otherSpokesCheck (.crossover 17) = true := by
  decide +kernel

private theorem otherSpokesCheck_case18 : otherSpokesCheck (.crossover 18) = true := by
  decide +kernel

private theorem otherSpokesCheck_case19 : otherSpokesCheck (.crossover 19) = true := by
  decide +kernel

private theorem otherSpokesCheck_case20 : otherSpokesCheck (.crossover 20) = true := by
  decide +kernel

private theorem otherSpokesCheck_case21 : otherSpokesCheck (.crossover 21) = true := by
  decide +kernel

private theorem otherSpokesCheck_case22 : otherSpokesCheck (.crossover 22) = true := by
  decide +kernel

private theorem otherSpokesCheck_case23 : otherSpokesCheck (.crossover 23) = true := by
  decide +kernel

private theorem otherSpokesCheck_case24 : otherSpokesCheck (.crossover 24) = true := by
  decide +kernel

private theorem otherSpokesCheck_case25 : otherSpokesCheck (.crossover 25) = true := by
  decide +kernel

private theorem otherSpokesCheck_case26 : otherSpokesCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem otherSpokesCheck_case27 : otherSpokesCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem otherSpokesCheck_case28 : otherSpokesCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem otherSpokesCheck_case29 : otherSpokesCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem otherSpokesCheck_case30 : otherSpokesCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem otherSpokesCheck_case31 : otherSpokesCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem otherSpokesCheck_case32 : otherSpokesCheck .routedClause = true := by
  decide +kernel

private theorem otherSpokesCheck_correct (kind : RetainedDirectClauseKind) :
    otherSpokesCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact otherSpokesCheck_case0
    · exact otherSpokesCheck_case1
    · exact otherSpokesCheck_case2
    · exact otherSpokesCheck_case3
    · exact otherSpokesCheck_case4
    · exact otherSpokesCheck_case5
    · exact otherSpokesCheck_case6
    · exact otherSpokesCheck_case7
    · exact otherSpokesCheck_case8
    · exact otherSpokesCheck_case9
    · exact otherSpokesCheck_case10
    · exact otherSpokesCheck_case11
    · exact otherSpokesCheck_case12
    · exact otherSpokesCheck_case13
    · exact otherSpokesCheck_case14
    · exact otherSpokesCheck_case15
    · exact otherSpokesCheck_case16
    · exact otherSpokesCheck_case17
    · exact otherSpokesCheck_case18
    · exact otherSpokesCheck_case19
    · exact otherSpokesCheck_case20
    · exact otherSpokesCheck_case21
    · exact otherSpokesCheck_case22
    · exact otherSpokesCheck_case23
    · exact otherSpokesCheck_case24
    · exact otherSpokesCheck_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact otherSpokesCheck_case26
      · exact otherSpokesCheck_case27
    | middle =>
      fin_cases index
      · exact otherSpokesCheck_case28
      · exact otherSpokesCheck_case29
    | right =>
      fin_cases index
      · exact otherSpokesCheck_case30
      · exact otherSpokesCheck_case31
  | routedClause => exact otherSpokesCheck_case32

/-- Exhaustive certificate for all same-center direct-prefix/other-spoke
interactions. -/
theorem retainedDirectSourceOtherFigure7SpokesSeparated :
    ∀ kind : RetainedDirectClauseKind,
      kind.SourceOtherFigure7SpokesSeparated := by
  intro kind index firstSlot secondSlot different
  have checked := otherSpokesCheck_correct kind
  simp only [otherSpokesCheck, finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact otherSpokeEntryCheck_sound kind index firstSlot secondSlot
    (checked index firstSlot secondSlot different)

/-- Pointwise local form of the exhaustive certificate. -/
theorem
    retainedDirectSourceFanCompleteRoute_strictlyAvoid_otherFigure7Spoke
    (kind : RetainedDirectClauseKind)
    (index :
      Fin (retainedDirectSourcePrefixChoices kind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index firstSlot)
      (retainedDirectSourceFigure7SpokeAt
        kind index secondSlot) :=
  retainedDirectSourceOtherFigure7SpokesSeparated
    kind index firstSlot secondSlot slotsDifferent

/-- The same certificate after positioning a checked final choice at its
physical component origin. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoid_otherFigure7Spoke
    (choice : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      (choice.figure7Spoke secondSlot) := by
  exact
    (retainedDirectSourceFanCompleteRoute_strictlyAvoid_otherFigure7Spoke
      choice.kind choice.index firstSlot secondSlot
      slotsDifferent).map_add
        (retainedDirectSourceFanPositioningOffset choice.origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
