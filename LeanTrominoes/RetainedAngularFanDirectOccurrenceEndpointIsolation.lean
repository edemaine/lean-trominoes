/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanDirectSourceCompleteCycleSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseOtherTargetSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification

/-!
# Terminal isolation of coordinated direct occurrences

The coordinated direct-source atlas is finite.  Its complete routes, including
the selected Figure 7 spoke, can therefore be checked once at the local origin.
Some collar walks revisit interior points, but none revisits its final Figure
7 endpoint.  Common translation transports exactly that terminal-isolation
property to every positioned direct choice.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- No finite local direct-atlas route, completed by any of the eight Figure
7 spokes, revisits its final endpoint after unit subdivision. -/
theorem
    retainedDirectSourceLocalChoice_completeFigure7Route_lastNotInDropLast :
    ∀ (kind : RetainedDirectClauseKind)
      (index :
        Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          ((retainedDirectSourceLocalChoice kind index)
            |>.completeFigure7Route slot)) := by
  intro kind index slot
  let choice := retainedDirectSourceLocalChoice kind index
  let center := retainedDirectSourceFanCenterAt kind index
  let suffix := retainedTerminalFanFigure7SpokeRouteAt center slot
  let cycle := retainedTerminalFanInnerCycleRouteAt center
    (.port (angularPortOfIndex slot.val)) ⟨0, by decide⟩
  have spokeEq : choice.figure7Spoke slot = suffix := by
    unfold RetainedDirectSourceRouteChoice.figure7Spoke retainedDirectSourceFigure7SpokeAt
      suffix retainedTerminalFanFigure7SpokeRouteAt
    simp only [choice, retainedDirectSourceLocalChoice,
      retainedDirectSourceFanPositioningOffset_zero, translatePolyline, List.map_map]
    apply List.map_congr_left
    intro point _
    apply Prod.ext <;> simp [Cell.add, Cell.sub, Cell.scale, center] <;> ring
  have cycleEq : choice.innerCycleRoute (.port (angularPortOfIndex slot.val)) 0 = cycle := by
    unfold RetainedDirectSourceRouteChoice.innerCycleRoute retainedDirectSourceInnerCycleRouteAt
      cycle retainedTerminalFanInnerCycleRouteAt retainedTerminalFanInnerCycleRoute
    simp only [choice, retainedDirectSourceLocalChoice,
      retainedDirectSourceFanPositioningOffset_zero, translatePolyline, List.map_map]
    apply List.map_congr_left
    intro point _
    apply Prod.ext <;> simp [Cell.add, Cell.sub, Cell.scale, center] <;> ring
  have prefixNonempty : choice.completeRoute slot ≠ [] := by
    intro empty
    have head := choice.completeRoute_head? slot
    simp [empty] at head
  have suffixLength : 2 ≤ suffix.length :=
    retainedTerminalFanFigure7SpokeRouteAt_length_ge_two center slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    simp [empty] at suffixLength
  let target := suffix.getLast suffixNonempty
  have suffixLast : suffix.getLast? = some target :=
    List.getLast?_eq_some_getLast suffixNonempty
  have cycleLast : cycle.getLast? = some target := by
    rw [← suffixLast]
    exact (retainedTerminalFanFigure7SpokeRouteAt_getLast?_eq_selectedInnerCycle center slot).symm
  have prefixLast := choice.completeRoute_getLast? slot
  have suffixHead := (congrArg List.head? spokeEq).symm.trans
    ((choice.figure7Spoke_head? slot).trans prefixLast)
  have strict : PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther (choice.completeRoute slot) cycle := by
    rw [← cycleEq]
    exact choice.completeRoute_strictlyAvoids_innerCycle slot _ 0
  change AxisDirection.LastNotInDropLast (AxisDirection.unitSubdividePolyline
    (joinAtEndpoint (choice.completeRoute slot) (choice.figure7Spoke slot)))
  rw [spokeEq]
  exact AxisDirection.lastNotInDropLast_unitSubdividePolyline_joinAtEndpoint_of_strictCycle
    prefixNonempty suffixLength (choice.completeRoute_orthogonal slot)
    (retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot)
    (retainedTerminalFanSelectedInnerCycleRouteAt_orthogonal center slot)
    prefixLast suffixHead suffixLast cycleLast strict
    (retainedTerminalFanFigure7SpokeRouteAt_isSimple center slot)

/-- The variable endpoint of every positioned direct occurrence is isolated
after unit subdivision. -/
theorem RetainedDirectSourceRouteChoice.completeFigure7Route_lastNotInDropLast
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (choice.completeFigure7Route slot)) := by
  let localChoice :=
    retainedDirectSourceLocalChoice choice.kind choice.index
  have choiceEq :
      choice = localChoice.translateOrigin choice.origin := by
    rcases choice with ⟨origin, kind, index⟩
    simp [localChoice, retainedDirectSourceLocalChoice,
      RetainedDirectSourceRouteChoice.translateOrigin, Cell.add]
  rw [choiceEq,
    RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
  exact
    (retainedDirectSourceLocalChoice_completeFigure7Route_lastNotInDropLast
      choice.kind choice.index slot).unitSubdividePolyline_map_add
        (retainedDirectSourceFanPositioningOffset choice.origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
