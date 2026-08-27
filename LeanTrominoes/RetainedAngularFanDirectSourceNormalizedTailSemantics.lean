/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedTailIndexSemantics

/-! # Semantics of complete normalized direct-source tail queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Gadget
open PeriodicOrthocrossing

/-- Translation to an arbitrary selected component origin leaves the entire
normalized route direction word equal to the finite origin-zero lookup. -/
theorem RetainedDirectSourceRouteChoice.normalizedCompleteFigure7Route_directions
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (choice.completeFigure7Route slot)) =
      retainedDirectSourceNormalizedDirectionsOfTailQuery
        (retainedDirectSourceNormalizedTailQueryOfIndex
          choice.kind choice.index slot) := by
  rw [retainedDirectSourceNormalizedDirectionsOfTailQuery_index]
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
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          ((zeroChoice.completeFigure7Route slot).map
            (Cell.add (retainedDirectSourceFanPositioningOffset origin)))) = _
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    (retainedDirectSourceZeroCompleteFigure7Route_valid
      kind index slot).1
    (retainedDirectSourceZeroCompleteFigure7Route_valid
      kind index slot).2]
  exact unitSubdivisionDirections_translatePolyline _ _

/-- The complete dynamic tail of an arbitrary selected direct route is the
finite query word with its first direction removed. -/
theorem RetainedDirectSourceRouteChoice.normalizedCompleteFigure7Route_tail
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    (unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (choice.completeFigure7Route slot))).tail =
      retainedDirectSourceNormalizedTailOfQuery
        (retainedDirectSourceNormalizedTailQueryOfIndex
          choice.kind choice.index slot) := by
  unfold retainedDirectSourceNormalizedTailOfQuery
  rw [choice.normalizedCompleteFigure7Route_directions]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
