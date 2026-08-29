/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixRayDirectionSemantics

/-! # Direction decomposition of ordinary and escaped fallback outer fans -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- The ordinary outer radial route consists of its finite lane shift and
the dynamic inward-ray word. -/
theorem retainedTerminalFanOuterRadialRoute_directions
    (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterRadialRoute center terminal slot) =
      prefixDirections .ordinary terminal.1 slot ++
        radialCopies
          (retainedTerminalFanOuterRadialLength terminal) terminal.1 := by
  unfold retainedTerminalFanOuterRadialRoute
  dsimp only
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · unfold prefixDirections retainedTerminalFanOuterLaneShiftRouteAt
    rw [Gadget.unitSubdivisionDirections_translatePolyline]
    change _ ++
        Gadget.unitSubdivisionDirections
          ((retainedTerminalFanOuterInwardRayOfLength terminal.1
            (retainedTerminalFanOuterRadialLength terminal)).rasterize _) = _
    rw [retainedTerminalFanOuterInwardRayOfLength_directions]
  · intro empty
    have head := retainedTerminalFanOuterLaneShiftRouteAt_head?
      (retainedAngularFanOuterDemand center terminal slot).gate
      terminal.1 slot
    simp [empty] at head
  · rw [retainedTerminalFanOuterLaneShiftRouteAt_getLast?,
      RetainedRay.rasterize_head?]

/-- The escaped outer radial route emits its fixed source escape and lane
shift before the remaining dynamic inward-ray word. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_directions
    (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterEscapedRadialRoute center terminal slot) =
      prefixDirections .escaped terminal.1 slot ++
        radialCopies
          (retainedTerminalFanOuterRadialLength terminal -
            retainedTerminalFanOuterSourceEscapeLength)
          terminal.1 := by
  unfold retainedTerminalFanOuterEscapedRadialRoute
  dsimp only
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
    · simp only [prefixDirections]
      unfold retainedTerminalFanOuterSourceEscapeRay
      rw [retainedTerminalFanOuterInwardRayOfLength_directions,
        show Gadget.unitSubdivisionDirections
            (retainedTerminalFanOuterLaneShiftRouteAt
              (retainedTerminalFanOuterSourceEscapePoint
                center terminal slot) terminal.1 slot) =
          Gadget.unitSubdivisionDirections
            (retainedTerminalFanOuterLaneShiftRoute terminal.1 slot) by
          unfold retainedTerminalFanOuterLaneShiftRouteAt
          exact Gadget.unitSubdivisionDirections_translatePolyline _ _]
      unfold retainedTerminalFanOuterEscapedRemainingRay
      rw [retainedTerminalFanOuterInwardRayOfLength_directions]
      simp [List.append_assoc]
      exact
        (retainedTerminalFanOuterInwardRayOfLength_directions terminal.1
          retainedTerminalFanOuterSourceEscapeLength (0, 0)).symm
    · intro empty
      have head := retainedTerminalFanOuterLaneShiftRouteAt_head?
        (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
        terminal.1 slot
      simp [empty] at head
    · rw [retainedTerminalFanOuterLaneShiftRouteAt_getLast?,
        RetainedRay.rasterize_head?]
  · intro empty
    have head := RetainedRay.rasterize_head?
      (retainedTerminalFanOuterSourceEscapeRay terminal)
      (retainedAngularFanOuterDemand center terminal slot).gate
    simp [empty] at head
  · have joinedHead :
        (joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot) terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
            (Cell.add
              (retainedTerminalFanOuterSourceEscapePoint
                center terminal slot)
              (retainedTerminalFanOuterLaneOffset
                terminal.1 slot)))).head? =
          some
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot) :=
        joinAtEndpoint_head?
          (retainedTerminalFanOuterLaneShiftRouteAt_head?
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot) terminal.1 slot)
    rw [RetainedRay.rasterize_getLast?, joinedHead]
    rfl

/-- A positive ordinary complete outer route appends its finite local-fan
adapter to the radial word. -/
theorem retainedTerminalFanOuterCompleteRoute_directions
    (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterCompleteRoute center terminal slot) =
      prefixDirections .ordinary terminal.1 slot ++
        radialCopies
            (retainedTerminalFanOuterRadialLength terminal) terminal.1 ++
          Gadget.unitSubdivisionDirections
            (retainedTerminalFanOuterLocalRouteAt
              center terminal.1 slot) := by
  unfold retainedTerminalFanOuterCompleteRoute
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · rw [retainedTerminalFanOuterRadialRoute_directions]
  · intro empty
    have head := retainedTerminalFanOuterRadialRoute_head?
      center terminal slot
    simp [empty] at head
  · rw [retainedTerminalFanOuterRadialRoute_getLast?
      center terminal slot lengthPositive,
      retainedTerminalFanOuterLocalRouteAt_head?]

/-- A positive valid escaped complete outer route appends the same finite
local-fan adapter after its delayed radial word. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_directions
    (center : Cell) (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : RetainedFallbackFanKind.escaped.Valid terminal) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot) =
      prefixDirections .escaped terminal.1 slot ++
        radialCopies
            (retainedTerminalFanOuterRadialLength terminal -
              retainedTerminalFanOuterSourceEscapeLength) terminal.1 ++
          Gadget.unitSubdivisionDirections
            (retainedTerminalFanOuterLocalRouteAt
              center terminal.1 slot) := by
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · rw [retainedTerminalFanOuterEscapedRadialRoute_directions]
  · intro empty
    have head := retainedTerminalFanOuterEscapedRadialRoute_head?
      center terminal slot
    simp [empty] at head
  · rw [retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center terminal slot lengthPositive valid,
      retainedTerminalFanOuterLocalRouteAt_head?]

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
