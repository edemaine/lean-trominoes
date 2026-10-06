/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteHull
import LeanTrominoes.OrthogonalPolylineBoundingBox

/-! Rectangle bounds for complete routes from their small linear hulls. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem retainedDirectSourceCompleteRouteHull_rectangleBounds
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (lower upper : Cell)
    (bounded : ∀ point ∈ retainedDirectSourceCompleteRouteHull kind index slot,
      InClosedGridRectangle lower upper point)
    {point : Cell} (member : point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot) :
    InClosedGridRectangle lower upper point := by
  have xBounds := retainedDirectSourceCompleteRouteHull_linearBounds kind index slot (1, 0)
    lower.1 upper.1 (fun p hp => by
      have h := bounded p hp
      simpa [Cell.linearValue, InClosedGridRectangle] using ⟨h.1, h.2.1⟩) member
  have yBounds := retainedDirectSourceCompleteRouteHull_linearBounds kind index slot (0, 1)
    lower.2 upper.2 (fun p hp => by
      have h := bounded p hp
      simpa [Cell.linearValue, InClosedGridRectangle] using ⟨h.2.2.1, h.2.2.2⟩) member
  exact ⟨by simpa [Cell.linearValue] using xBounds.1,
    by simpa [Cell.linearValue] using xBounds.2,
    by simpa [Cell.linearValue] using yBounds.1,
    by simpa [Cell.linearValue] using yBounds.2⟩

end LeanTrominoes.PeriodicEightOccurrenceSplit
