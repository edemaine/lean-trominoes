import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
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
  have checked :
      ∀ (kind : RetainedDirectClauseKind)
        (index :
          Fin (retainedDirectSourcePrefixChoices kind).length)
        (slot : RetainedTerminalSlot),
        let route :=
          AxisDirection.unitSubdividePolyline
            ((retainedDirectSourceLocalChoice kind index)
              |>.completeFigure7Route slot)
        route.getLastD (0, 0) ∉ route.dropLast := by
    native_decide
  intro kind index slot
  exact
    AxisDirection.lastNotInDropLast_of_getLastD_not_mem
      (checked kind index slot)

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
