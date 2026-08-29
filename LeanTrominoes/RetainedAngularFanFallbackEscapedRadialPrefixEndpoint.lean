/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackEscapedRadialPrefixData

/-! # Endpoint of the escaped fallback radial prefix -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 4096

/-- The fixed source escape and the shortened remaining ray together have
the displacement of the full inward ray with its final primitive removed. -/
theorem retainedTerminalFanOuterEscapedPrefixRay_vectors_add
    (terminal : RetainedTerminalData)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    Cell.add
        (retainedTerminalFanOuterSourceEscapeRay terminal).vector
        (retainedTerminalFanOuterEscapedRemainingPrefixRay terminal).vector =
      (retainedTerminalFanOuterInwardPrefixRay terminal).vector := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterEscapedRemainingPrefixRay,
          retainedTerminalFanOuterInwardPrefixRay,
          retainedTerminalFanOuterInwardRayOfLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalInterfaceMultiplier,
          RetainedRay.vector, oppositePort,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale] at escapeStrict ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterEscapedRemainingPrefixRay,
          retainedTerminalFanOuterInwardPrefixRay,
          retainedTerminalFanOuterInwardRayOfLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalInterfaceMultiplier,
          RetainedRay.vector, routedClauseRayPrimitive,
          Cell.add, Cell.scale] at escapeStrict ⊢ <;>
        omega

/-- With a nonempty remaining radial suffix, the escaped exterior prefix
ends one primitive outside the selected lane port. -/
@[simp]
theorem retainedTerminalFanOuterEscapedRadialPrefix_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterEscapedRadialPrefix
      center terminal slot).getLast? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
              terminal.1.primitive)) := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  have escapePointEq :
      escapePoint =
        Cell.add gate
          (retainedTerminalFanOuterSourceEscapeRay terminal).vector := by
    rfl
  have shiftedEscapePointEq :
      shiftedEscapePoint =
        Cell.add escapePoint
          (retainedTerminalFanOuterLaneOffset terminal.1 slot) := by
    rfl
  have escapeLast :
      ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
        gate).getLast? = some escapePoint := by
    rw [RetainedRay.rasterize_getLast?]
    rfl
  have prefixLast :
      ((retainedTerminalFanOuterEscapedRemainingPrefixRay terminal).rasterize
        shiftedEscapePoint).getLast? =
          some
            (Cell.add center
              (Cell.add
                (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
                terminal.1.primitive)) := by
    rw [RetainedRay.rasterize_getLast?]
    apply congrArg some
    calc
      Cell.add shiftedEscapePoint
          (retainedTerminalFanOuterEscapedRemainingPrefixRay
            terminal).vector =
        Cell.add
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))
          (retainedTerminalFanOuterInwardPrefixRay terminal).vector := by
            rw [shiftedEscapePointEq, escapePointEq,
              ← retainedTerminalFanOuterEscapedPrefixRay_vectors_add
                terminal escapeStrict]
            rcases gate with ⟨gateX, gateY⟩
            rcases
                (retainedTerminalFanOuterSourceEscapeRay terminal).vector with
              ⟨escapeX, escapeY⟩
            rcases
                (retainedTerminalFanOuterEscapedRemainingPrefixRay
                  terminal).vector with
              ⟨remainingX, remainingY⟩
            rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
              ⟨offsetX, offsetY⟩
            simp [Cell.add]
            constructor <;> ring
      _ = Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
            terminal.1.primitive) :=
        retainedTerminalFanOuterInwardPrefix_finish_eq
          center terminal slot (by omega)
  unfold retainedTerminalFanOuterEscapedRadialPrefix
  apply joinAtEndpoint_getLast? escapeLast
  · apply joinAtEndpoint_head?
    exact retainedTerminalFanOuterLaneShiftRouteAt_head?
      escapePoint terminal.1 slot
  · apply joinAtEndpoint_getLast?
      (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
        escapePoint terminal.1 slot)
      (RetainedRay.rasterize_head?
        (retainedTerminalFanOuterEscapedRemainingPrefixRay terminal)
        shiftedEscapePoint)
      prefixLast

end PeriodicEightOccurrenceSplit
end LeanTrominoes
