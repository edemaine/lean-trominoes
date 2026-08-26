/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionTranslation
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Clause-side ordering of coordinated direct-source routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

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
  native_decide

/-- Every tabulated direct-source direction is a genuine cardinal
direction. -/
theorem retainedDirectSourceCoordinatedFirstDirection_isGenuine :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      (retainedDirectSourceCoordinatedFirstDirection kind index).IsGenuine := by
  native_decide

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
