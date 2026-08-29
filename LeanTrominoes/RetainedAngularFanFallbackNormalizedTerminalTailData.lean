/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackNormalizedFiniteTailData
import LeanTrominoes.RetainedAngularFanOuterRadialFinalStubs

/-! # Normalized terminal tails of fallback fan routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The fixed end of a positive fallback radial route, including its final
primitive block, local adapter, and matching Figure 7 spoke.  Including the
final primitive block lets the compiler normalize every possible local loop
inside one finite table. -/
def retainedFallbackFanTerminalTailRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterRadialFinalStubAt center direction slot)
    (retainedFallbackFanFiniteTailRouteAt center direction slot)

/-- Every fixed terminal tail is nonempty. -/
theorem retainedFallbackFanTerminalTailRouteAt_ne_nil
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    retainedFallbackFanTerminalTailRouteAt
      center direction slot ≠ [] := by
  intro empty
  have head :
      (retainedFallbackFanTerminalTailRouteAt
        center direction slot).head? =
          some
            (Cell.add center
              (Cell.add
                (retainedTerminalFanOuterLanePortOffset direction slot)
                direction.primitive)) := by
    unfold retainedFallbackFanTerminalTailRouteAt
    exact joinAtEndpoint_head?
      (second := retainedFallbackFanFiniteTailRouteAt
        center direction slot)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center direction slot)
  rw [empty] at head
  simp at head

/-- The final primitive block meets the finite local-and-spoke tail at the
advertised lane port, so their fixed terminal tail is orthogonal. -/
theorem retainedFallbackFanTerminalTailRouteAt_orthogonal
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedFallbackFanTerminalTailRouteAt
        center direction slot) := by
  have finiteTailHead :
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
  exact
    (retainedTerminalFanOuterRadialFinalStubAt_orthogonal
      center direction slot).joinAtEndpoint
      (retainedFallbackFanFiniteTailRouteAt_orthogonal
        center direction slot)
      (retainedTerminalFanOuterRadialFinalStubAt_getLast?
        center direction slot)
      finiteTailHead

/-- Translating the fan center translates its final radial primitive. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_translatePolyline
    (offset center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterRadialFinalStubAt
          center direction slot) =
      retainedTerminalFanOuterRadialFinalStubAt
        (Cell.add offset center) direction slot := by
  unfold retainedTerminalFanOuterRadialFinalStubAt translatePolyline
  rw [List.map_map]
  congr 1
  funext point
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add, add_assoc]

/-- Translating the fan center translates its complete fixed terminal tail. -/
theorem retainedFallbackFanTerminalTailRouteAt_translatePolyline
    (offset center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedFallbackFanTerminalTailRouteAt
          center direction slot) =
      retainedFallbackFanTerminalTailRouteAt
        (Cell.add offset center) direction slot := by
  unfold retainedFallbackFanTerminalTailRouteAt
  rw [translatePolyline_joinAtEndpoint,
    retainedTerminalFanOuterRadialFinalStubAt_translatePolyline,
    retainedFallbackFanFiniteTailRouteAt_translatePolyline]

/-- The 88 origin-zero normalized terminal-tail words form the fixed output
table used after the dynamic exterior radial prefix. -/
def retainedFallbackFanNormalizedTerminalTailDirections
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      (retainedFallbackFanTerminalTailRouteAt
        (0, 0) direction slot))

/-- Positioning a fixed terminal tail does not change its normalized
direction word. -/
theorem retainedFallbackFanTerminalTailRouteAt_normalized_directions
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanTerminalTailRouteAt
            center direction slot)) =
      retainedFallbackFanNormalizedTerminalTailDirections
        direction slot := by
  let zeroTail := retainedFallbackFanTerminalTailRouteAt
    (0, 0) direction slot
  have zeroTailNonempty : zeroTail ≠ [] :=
    retainedFallbackFanTerminalTailRouteAt_ne_nil
      (0, 0) direction slot
  have zeroTailOrthogonal : OrthogonalPolyline zeroTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      (0, 0) direction slot
  have translated :=
    retainedFallbackFanTerminalTailRouteAt_translatePolyline
      center (0, 0) direction slot
  simp only [Cell.add_zero] at translated
  rw [← translated]
  unfold translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    zeroTailNonempty zeroTailOrthogonal center]
  unfold retainedFallbackFanNormalizedTerminalTailDirections
  exact Gadget.unitSubdivisionDirections_translatePolyline center _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
