/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanOuterRouteTranslation

/-! # Normalized finite tails of fallback fan routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Fixed tail after the dynamic outer radial route: the local adapter joined
to the matching Figure 7 spoke. -/
def retainedFallbackFanFiniteTailRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterLocalRouteAt center direction slot)
    (retainedTerminalFanFigure7SpokeRouteAt center slot)

/-- Every fixed fallback tail is nonempty. -/
theorem retainedFallbackFanFiniteTailRouteAt_ne_nil
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    retainedFallbackFanFiniteTailRouteAt
      center direction slot ≠ [] := by
  intro empty
  have head :
      (retainedFallbackFanFiniteTailRouteAt
        center direction slot).head? =
          some
            (retainedTerminalFanOuterLanePort
              center direction slot) := by
    unfold retainedFallbackFanFiniteTailRouteAt
    exact joinAtEndpoint_head?
      (second := retainedTerminalFanFigure7SpokeRouteAt center slot)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center direction slot)
  rw [empty] at head
  simp at head

/-- The local adapter and spoke meet at their advertised boundary, so the
fixed tail is orthogonal even though it can contain loops. -/
theorem retainedFallbackFanFiniteTailRouteAt_orthogonal
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedFallbackFanFiniteTailRouteAt
        center direction slot) := by
  exact
    (retainedTerminalFanOuterLocalRouteAt_orthogonal
      center direction slot).joinAtEndpoint
      (retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot)
      (retainedTerminalFanOuterLocalRouteAt_getLast?
        center direction slot)
      (retainedTerminalFanFigure7SpokeRouteAt_head? center slot)

/-- Translating the fan center translates its complete fixed tail. -/
theorem retainedFallbackFanFiniteTailRouteAt_translatePolyline
    (offset center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedFallbackFanFiniteTailRouteAt
          center direction slot) =
      retainedFallbackFanFiniteTailRouteAt
        (Cell.add offset center) direction slot := by
  unfold retainedFallbackFanFiniteTailRouteAt
  rw [translatePolyline_joinAtEndpoint,
    retainedTerminalFanOuterLocalRouteAt_translatePolyline]
  unfold retainedTerminalFanFigure7SpokeRouteAt
    translatePolyline
  rw [List.map_map]
  congr 2
  funext point
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]
  constructor <;> ring

/-- The 88 origin-zero loop-erased finite-tail words form the fixed output
table used by the normalized suffix compiler. -/
def retainedFallbackFanNormalizedFiniteTailDirections
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      (retainedFallbackFanFiniteTailRouteAt
        (0, 0) direction slot))

/-- Positioning a fixed tail does not change its normalized direction word. -/
theorem retainedFallbackFanFiniteTailRouteAt_normalized_directions
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanFiniteTailRouteAt
            center direction slot)) =
      retainedFallbackFanNormalizedFiniteTailDirections
        direction slot := by
  let zeroTail := retainedFallbackFanFiniteTailRouteAt
    (0, 0) direction slot
  have zeroTailNonempty : zeroTail ≠ [] :=
    retainedFallbackFanFiniteTailRouteAt_ne_nil
      (0, 0) direction slot
  have zeroTailOrthogonal : OrthogonalPolyline zeroTail :=
    retainedFallbackFanFiniteTailRouteAt_orthogonal
      (0, 0) direction slot
  have translated :=
    retainedFallbackFanFiniteTailRouteAt_translatePolyline
      center (0, 0) direction slot
  simp only [Cell.add_zero] at translated
  rw [← translated]
  unfold translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    zeroTailNonempty zeroTailOrthogonal center]
  unfold retainedFallbackFanNormalizedFiniteTailDirections
  exact Gadget.unitSubdivisionDirections_translatePolyline center _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
