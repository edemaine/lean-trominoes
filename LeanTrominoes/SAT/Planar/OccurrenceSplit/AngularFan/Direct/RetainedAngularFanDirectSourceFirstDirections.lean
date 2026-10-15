/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineScaling
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineEndpointDirectionTranslation
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceCompleteCycleSeparation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceCrossClauseOtherTargetSeparation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Coordinated.RetainedAngularFanFinalCoordinatedRoutes

/-! # Clause-side ordering of coordinated direct-source routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest =>
          rfl

private def escapeDirectionsCorrect (kind : RetainedDirectClauseKind) : Prop :=
  ∀ (index : Fin (retainedDirectSourcePrefixChoices kind).length) (slot : RetainedTerminalSlot),
    AxisDirection.polylineFirstDirection (retainedDirectSourceFanEscapeAt kind index slot).route =
      AxisDirection.polylineFirstDirection (retainedDirectSourceFanEscapeAt kind index 0).route ∧
    (AxisDirection.polylineFirstDirection (retainedDirectSourceFanEscapeAt kind index slot).route).IsGenuine

private theorem escapeDirectionsCorrect_case0 : escapeDirectionsCorrect (.crossover 0) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case1 : escapeDirectionsCorrect (.crossover 1) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case2 : escapeDirectionsCorrect (.crossover 2) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case3 : escapeDirectionsCorrect (.crossover 3) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case4 : escapeDirectionsCorrect (.crossover 4) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case5 : escapeDirectionsCorrect (.crossover 5) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case6 : escapeDirectionsCorrect (.crossover 6) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case7 : escapeDirectionsCorrect (.crossover 7) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case8 : escapeDirectionsCorrect (.crossover 8) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case9 : escapeDirectionsCorrect (.crossover 9) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case10 : escapeDirectionsCorrect (.crossover 10) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case11 : escapeDirectionsCorrect (.crossover 11) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case12 : escapeDirectionsCorrect (.crossover 12) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case13 : escapeDirectionsCorrect (.crossover 13) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case14 : escapeDirectionsCorrect (.crossover 14) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case15 : escapeDirectionsCorrect (.crossover 15) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case16 : escapeDirectionsCorrect (.crossover 16) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case17 : escapeDirectionsCorrect (.crossover 17) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case18 : escapeDirectionsCorrect (.crossover 18) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case19 : escapeDirectionsCorrect (.crossover 19) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case20 : escapeDirectionsCorrect (.crossover 20) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case21 : escapeDirectionsCorrect (.crossover 21) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case22 : escapeDirectionsCorrect (.crossover 22) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case23 : escapeDirectionsCorrect (.crossover 23) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case24 : escapeDirectionsCorrect (.crossover 24) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case25 : escapeDirectionsCorrect (.crossover 25) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case26 : escapeDirectionsCorrect (.duplicator .left 0) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case27 : escapeDirectionsCorrect (.duplicator .left 1) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case28 : escapeDirectionsCorrect (.duplicator .middle 0) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case29 : escapeDirectionsCorrect (.duplicator .middle 1) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case30 : escapeDirectionsCorrect (.duplicator .right 0) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case31 : escapeDirectionsCorrect (.duplicator .right 1) := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_case32 : escapeDirectionsCorrect .routedClause := by
  unfold escapeDirectionsCorrect
  decide +kernel

private theorem escapeDirectionsCorrect_ok (kind : RetainedDirectClauseKind) :
    escapeDirectionsCorrect kind := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact escapeDirectionsCorrect_case0
    · exact escapeDirectionsCorrect_case1
    · exact escapeDirectionsCorrect_case2
    · exact escapeDirectionsCorrect_case3
    · exact escapeDirectionsCorrect_case4
    · exact escapeDirectionsCorrect_case5
    · exact escapeDirectionsCorrect_case6
    · exact escapeDirectionsCorrect_case7
    · exact escapeDirectionsCorrect_case8
    · exact escapeDirectionsCorrect_case9
    · exact escapeDirectionsCorrect_case10
    · exact escapeDirectionsCorrect_case11
    · exact escapeDirectionsCorrect_case12
    · exact escapeDirectionsCorrect_case13
    · exact escapeDirectionsCorrect_case14
    · exact escapeDirectionsCorrect_case15
    · exact escapeDirectionsCorrect_case16
    · exact escapeDirectionsCorrect_case17
    · exact escapeDirectionsCorrect_case18
    · exact escapeDirectionsCorrect_case19
    · exact escapeDirectionsCorrect_case20
    · exact escapeDirectionsCorrect_case21
    · exact escapeDirectionsCorrect_case22
    · exact escapeDirectionsCorrect_case23
    · exact escapeDirectionsCorrect_case24
    · exact escapeDirectionsCorrect_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact escapeDirectionsCorrect_case26
      · exact escapeDirectionsCorrect_case27
    | middle =>
      fin_cases index
      · exact escapeDirectionsCorrect_case28
      · exact escapeDirectionsCorrect_case29
    | right =>
      fin_cases index
      · exact escapeDirectionsCorrect_case30
      · exact escapeDirectionsCorrect_case31
  | routedClause => exact escapeDirectionsCorrect_case32

private theorem completeFirst_eq_escape (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) (slot : RetainedTerminalSlot) :
    AxisDirection.polylineFirstDirection (retainedDirectSourceFanCompleteRouteAt kind index slot) =
      AxisDirection.polylineFirstDirection (retainedDirectSourceFanEscapeAt kind index slot).route := by
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let escape := retainedDirectSourceFanEscapeAt kind index slot
  have genuine := (escapeDirectionsCorrect_ok kind index slot).2
  have radialEq : AxisDirection.polylineFirstDirection
      (retainedTerminalFanOuterCoordinatedEscapedRadialRoute center terminal slot escape) =
      AxisDirection.polylineFirstDirection escape.route := by
    unfold retainedTerminalFanOuterCoordinatedEscapedRadialRoute
    exact polylineFirstDirection_joinAtEndpoint_of_genuine genuine
  have radialGenuine : (AxisDirection.polylineFirstDirection
      (retainedTerminalFanOuterCoordinatedEscapedRadialRoute center terminal slot escape)).IsGenuine := by
    rw [radialEq]
    exact genuine
  change AxisDirection.polylineFirstDirection (joinAtEndpoint
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute center terminal slot escape)
    (retainedTerminalFanOuterLocalRouteAt center terminal.1 slot)) = _
  exact (polylineFirstDirection_joinAtEndpoint_of_genuine radialGenuine).trans radialEq

/-- Finite lookup table for the clause-side direction of one coordinated
direct-source atlas entry. -/
def retainedDirectSourceCoordinatedFirstDirection
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    AxisDirection :=
  AxisDirection.polylineFirstDirection
    (retainedDirectSourceFanCompleteRouteAt kind index ⟨0, by decide⟩)

/-- The clause-side direction of a coordinated direct-source route depends
only on its finite atlas entry, not on its variable-side occurrence slot. -/
theorem retainedDirectSourceFanCompleteRouteAt_firstDirection_eq :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      AxisDirection.polylineFirstDirection
          (retainedDirectSourceFanCompleteRouteAt kind index slot) =
        retainedDirectSourceCoordinatedFirstDirection kind index := by
  intro kind index slot
  unfold retainedDirectSourceCoordinatedFirstDirection
  rw [completeFirst_eq_escape, completeFirst_eq_escape]
  exact (escapeDirectionsCorrect_ok kind index slot).1

/-- Every tabulated direct-source direction is a genuine cardinal
direction. -/
theorem retainedDirectSourceCoordinatedFirstDirection_isGenuine :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      (retainedDirectSourceCoordinatedFirstDirection kind index).IsGenuine := by
  intro kind index
  unfold retainedDirectSourceCoordinatedFirstDirection
  rw [completeFirst_eq_escape]
  exact (escapeDirectionsCorrect_ok kind index 0).2

/-- Canonical origin-zero representative of one direct-source atlas entry. -/
def retainedDirectSourceZeroChoice
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedDirectSourceRouteChoice where
  origin := (0, 0)
  kind := kind
  index := index

/-- Finite lookup table for the clause-side direction after the direct
Figure 7 occurrence route has been normalized. -/
def retainedDirectSourceNormalizedFirstDirection
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : AxisDirection :=
  AxisDirection.polylineFirstDirection
    (AxisDirection.normalizeOrthogonalPolyline
      ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
        slot))

/-- Every origin-zero complete direct Figure 7 occurrence is nonempty and
orthogonal, the hypotheses needed to transport normalization through a
component translation. -/
theorem retainedDirectSourceZeroCompleteFigure7Route_valid :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      (retainedDirectSourceZeroChoice kind index).completeFigure7Route slot ≠
          [] ∧
        PeriodicOrthocrossing.OrthogonalPolyline
          ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
            slot) := by
  intro kind index slot
  let choice := retainedDirectSourceZeroChoice kind index
  have spokeOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline (choice.figure7Spoke slot) := by
    unfold RetainedDirectSourceRouteChoice.figure7Spoke retainedDirectSourceFigure7SpokeAt
    apply PeriodicOrthocrossing.OrthogonalPolyline.translate
    apply PeriodicOrthocrossing.OrthogonalPolyline.translate
    apply PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
    · generalize angularPortOfIndex slot.val = port
      cases port <;> decide +kernel
    · decide
  have prefixLast := choice.completeRoute_getLast? slot
  have spokeHead := (choice.figure7Spoke_head? slot).trans prefixLast
  have head := joinAtEndpoint_head? (second := choice.figure7Spoke slot)
    (choice.completeRoute_head? slot)
  change joinAtEndpoint (choice.completeRoute slot) (choice.figure7Spoke slot) ≠ [] ∧ _
  refine ⟨?_, ?_⟩
  · intro empty
    simp [empty] at head
  · exact PeriodicOrthocrossing.OrthogonalPolyline.joinAtEndpoint
      (choice.completeRoute_orthogonal slot) spokeOrthogonal prefixLast spokeHead

/-- Translation to an arbitrary component origin commutes with normalization,
so the finite origin-zero table gives the exact normalized first direction. -/
theorem RetainedDirectSourceRouteChoice.normalizedCompleteFigure7Route_firstDirection
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (choice.completeFigure7Route slot)) =
      retainedDirectSourceNormalizedFirstDirection
        choice.kind choice.index slot := by
  rcases choice with ⟨origin, kind, index⟩
  let zeroChoice := retainedDirectSourceZeroChoice kind index
  have choiceEq :
      ({ origin := origin, kind := kind, index := index } :
          RetainedDirectSourceRouteChoice) =
        zeroChoice.translateOrigin origin := by
    simp [zeroChoice, retainedDirectSourceZeroChoice,
      RetainedDirectSourceRouteChoice.translateOrigin, Cell.add]
  rw [choiceEq,
    RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          ((zeroChoice.completeFigure7Route slot).map
            (Cell.add (retainedDirectSourceFanPositioningOffset origin)))) =
      retainedDirectSourceNormalizedFirstDirection kind index slot
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    (retainedDirectSourceZeroCompleteFigure7Route_valid
      kind index slot).1
    (retainedDirectSourceZeroCompleteFigure7Route_valid
      kind index slot).2]
  change
    AxisDirection.polylineFirstDirection
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset origin)
          (AxisDirection.normalizeOrthogonalPolyline
            ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
              slot))) = _
  rw [AxisDirection.polylineFirstDirection_translatePolyline_static]
  rfl

/-- Translating a selected atlas route into its final component coordinates
does not change its tabulated first direction. -/
theorem RetainedDirectSourceRouteChoice.completeRoute_firstDirection
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    AxisDirection.polylineFirstDirection (choice.completeRoute slot) =
      retainedDirectSourceCoordinatedFirstDirection
        choice.kind choice.index := by
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
  rw [AxisDirection.polylineFirstDirection_translatePolyline_static]
  exact retainedDirectSourceFanCompleteRouteAt_firstDirection_eq
    choice.kind choice.index slot

/-- Appending the unchanged Figure 7 suffix leaves the finite coordinated
direct-source lookup visible at the public unnormalized route boundary. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice)
    (clause :
      PositionedPeriodicClause
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (PeriodicOrthocrossing.retainedFinalCoordinatedDirectOccurrenceRoute
          formula choice clause literal clauseIndex literalIndex) =
      retainedDirectSourceCoordinatedFirstDirection
        choice.kind choice.index := by
  unfold
    PeriodicOrthocrossing.retainedFinalCoordinatedDirectOccurrenceRoute
  rw [polylineFirstDirection_joinAtEndpoint_of_genuine]
  · exact choice.completeRoute_firstDirection _
  · rw [choice.completeRoute_firstDirection]
    exact retainedDirectSourceCoordinatedFirstDirection_isGenuine
      choice.kind choice.index

end PeriodicEightOccurrenceSplit
end LeanTrominoes
