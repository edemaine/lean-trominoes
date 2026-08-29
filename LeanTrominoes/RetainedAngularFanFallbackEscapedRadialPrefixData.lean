/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialDirectionSemantics

/-! # Exterior prefixes of escaped fallback radial routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- The escaped remaining ray with its final primitive block reserved for
the normalized terminal tail. -/
def retainedTerminalFanOuterEscapedRemainingPrefixRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  retainedTerminalFanOuterInwardRayOfLength terminal.1
    (retainedTerminalFanOuterRadialLength terminal -
      retainedTerminalFanOuterSourceEscapeLength - 1)

/-- The fixed part of an escaped radial route: its source escape followed
by its delayed occurrence-lane shift. -/
def retainedTerminalFanOuterEscapedFixedPrefix
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  joinAtEndpoint
    ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate)
    (retainedTerminalFanOuterLaneShiftRouteAt
      escapePoint terminal.1 slot)

@[simp]
theorem retainedTerminalFanOuterEscapedFixedPrefix_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedFixedPrefix
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  unfold retainedTerminalFanOuterEscapedFixedPrefix
  apply joinAtEndpoint_head?
  exact RetainedRay.rasterize_head? _ _

@[simp]
theorem retainedTerminalFanOuterEscapedFixedPrefix_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedFixedPrefix
      center terminal slot).getLast? =
        some
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot)
            (retainedTerminalFanOuterLaneOffset terminal.1 slot)) := by
  unfold retainedTerminalFanOuterEscapedFixedPrefix
  apply joinAtEndpoint_getLast?
    (by
      rw [RetainedRay.rasterize_getLast?]
      rfl)
    (retainedTerminalFanOuterLaneShiftRouteAt_head?
      (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
      terminal.1 slot)
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
      terminal.1 slot)

theorem retainedTerminalFanOuterEscapedFixedPrefix_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedTerminalFanOuterEscapedFixedPrefix
        center terminal slot) := by
  unfold retainedTerminalFanOuterEscapedFixedPrefix
  exact
    (RetainedRay.rasterize_orthogonal _ _).joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal _ _ _)
      (by
        rw [RetainedRay.rasterize_getLast?]
        rfl)
      (retainedTerminalFanOuterLaneShiftRouteAt_head? _ _ _)

/-- The fixed geometric prefix realizes the compiler's escaped prefix
direction table. -/
theorem retainedTerminalFanOuterEscapedFixedPrefix_directions
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterEscapedFixedPrefix
          center terminal slot) =
      prefixDirections .escaped terminal.1 slot := by
  unfold retainedTerminalFanOuterEscapedFixedPrefix
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
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
    exact congrArg
      (fun directions => directions ++
        Gadget.unitSubdivisionDirections
          (retainedTerminalFanOuterLaneShiftRoute terminal.1 slot))
      (retainedTerminalFanOuterInwardRayOfLength_directions terminal.1
        retainedTerminalFanOuterSourceEscapeLength (0, 0)).symm
  · intro empty
    have head := RetainedRay.rasterize_head?
      (retainedTerminalFanOuterSourceEscapeRay terminal)
      (retainedAngularFanOuterDemand center terminal slot).gate
    simp [empty] at head
  · rw [RetainedRay.rasterize_getLast?]
    rw [retainedTerminalFanOuterLaneShiftRouteAt_head?]
    rfl

/-- Source escape, delayed lane shift, and every remaining inward primitive
except the final block. -/
def retainedTerminalFanOuterEscapedRadialPrefix
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  joinAtEndpoint
    ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate)
    (joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        escapePoint terminal.1 slot)
      ((retainedTerminalFanOuterEscapedRemainingPrefixRay terminal).rasterize
        shiftedEscapePoint))

/-- Reassociate the escaped exterior prefix around its fixed prefix and
dynamic remaining ray. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_eq_fixedPrefix_join
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterEscapedRadialPrefix center terminal slot =
      joinAtEndpoint
        (retainedTerminalFanOuterEscapedFixedPrefix
          center terminal slot)
        ((retainedTerminalFanOuterEscapedRemainingPrefixRay terminal).rasterize
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))) := by
  unfold retainedTerminalFanOuterEscapedRadialPrefix
    retainedTerminalFanOuterEscapedFixedPrefix
  rw [joinAtEndpoint_assoc_of_middle_ne_nil]
  intro empty
  have head := retainedTerminalFanOuterLaneShiftRouteAt_head?
    (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
    terminal.1 slot
  simp [empty] at head

/-- The escaped exterior prefix begins at the unchanged source gate. -/
@[simp]
theorem retainedTerminalFanOuterEscapedRadialPrefix_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedRadialPrefix
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  unfold retainedTerminalFanOuterEscapedRadialPrefix
  apply joinAtEndpoint_head?
  exact RetainedRay.rasterize_head? _ _

/-- The escaped exterior prefix is an orthogonal endpoint join. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedTerminalFanOuterEscapedRadialPrefix
        center terminal slot) := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  have shiftedTailOrthogonal :
      OrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            escapePoint terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingPrefixRay
            terminal).rasterize shiftedEscapePoint)) := by
    exact
      (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
        escapePoint terminal.1 slot).joinAtEndpoint
        (RetainedRay.rasterize_orthogonal _ _)
        (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
          escapePoint terminal.1 slot)
        (RetainedRay.rasterize_head? _ _)
  unfold retainedTerminalFanOuterEscapedRadialPrefix
  exact
    (RetainedRay.rasterize_orthogonal
      (retainedTerminalFanOuterSourceEscapeRay terminal)
      gate).joinAtEndpoint
      shiftedTailOrthogonal
      (by rw [RetainedRay.rasterize_getLast?])
      (by
        apply joinAtEndpoint_head?
        exact retainedTerminalFanOuterLaneShiftRouteAt_head?
          escapePoint terminal.1 slot)

/-- Its direction word is the fixed escaped prefix followed by every
remaining radial primitive except the last. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_directions
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterEscapedRadialPrefix
          center terminal slot) =
      prefixDirections .escaped terminal.1 slot ++
        radialCopies
          (retainedTerminalFanOuterRadialLength terminal -
            retainedTerminalFanOuterSourceEscapeLength - 1)
          terminal.1 := by
  unfold retainedTerminalFanOuterEscapedRadialPrefix
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
      unfold retainedTerminalFanOuterEscapedRemainingPrefixRay
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
  · rw [RetainedRay.rasterize_getLast?]
    rw [joinAtEndpoint_head?
      (retainedTerminalFanOuterLaneShiftRouteAt_head?
        (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
        terminal.1 slot)]
    rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
