/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceEscapeAngularBounds
import LeanTrominoes.RetainedAngularFanDirectFallbackOuterReduction
import LeanTrominoes.RetainedAngularFanOuterEscapedRadialSeparation

/-!
# Direct source escape separation from fallback radial routes

The finite angular certificates for a selected direct escape combine with
the canonical radial-route bounds.  Thus strict compatible direction/slot
order separates the custom escape from either an ordinary or delayed-lane
fallback radial route at the same translated fan center.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A translated custom direct escape strictly avoids an ordinary fallback
radial route under strict compatible angular order. -/
theorem
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_ordinaryRadial_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (offset : Cell)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index directSlot).route)
      (retainedTerminalFanOuterRadialRoute
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        fallbackTerminal fallbackSlot) := by
  rcases angularOrder with
      ⟨slotsLt, directionsLt⟩ |
      ⟨slotsLt, directionsLt⟩
  · have directSlotLtSeven : directSlot.val < 7 := by
      have fallbackSlotLtEight := fallbackSlot.isLt
      omega
    have fallbackSlotPositive : 0 < fallbackSlot.val := by
      omega
    exact
      routesStrictlyAvoidEachOther_of_linear_separated
        (retainedTerminalFanOuterRadialSeparatorNormal
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.1)
        (Cell.linearValue
            (retainedTerminalFanOuterRadialSeparatorNormal
              (retainedDirectSourceFanTerminalAt kind index).1
              fallbackTerminal.1)
            (Cell.add offset
              (retainedDirectSourceFanCenterAt kind index)) +
          retainedTerminalFanOuterRadialSeparatorBound
            (retainedDirectSourceFanTerminalAt kind index).1
            fallbackTerminal.1)
        (retainedDirectSourceFanEscapeAt_translate_angular_linear_upper
          kind index directSlot fallbackTerminal.1 directionsLt
          directSlotLtSeven offset)
        (retainedTerminalFanOuterRadialRoute_linear_lower
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index))
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.1 fallbackTerminal.2 fallbackSlot
          directionsLt fallbackLengthPositive fallbackSlotPositive)
  · have fallbackSlotLtSeven : fallbackSlot.val < 7 := by
      have directSlotLtEight := directSlot.isLt
      omega
    have directSlotPositive : 0 < directSlot.val := by
      omega
    exact
      (routesStrictlyAvoidEachOther_of_linear_separated
        (retainedTerminalFanOuterRadialSeparatorNormal
          fallbackTerminal.1
          (retainedDirectSourceFanTerminalAt kind index).1)
        (Cell.linearValue
            (retainedTerminalFanOuterRadialSeparatorNormal
              fallbackTerminal.1
              (retainedDirectSourceFanTerminalAt kind index).1)
            (Cell.add offset
              (retainedDirectSourceFanCenterAt kind index)) +
          retainedTerminalFanOuterRadialSeparatorBound
            fallbackTerminal.1
            (retainedDirectSourceFanTerminalAt kind index).1)
        (retainedTerminalFanOuterRadialRoute_linear_upper
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index))
          fallbackTerminal.1
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.2 fallbackSlot directionsLt
          fallbackLengthPositive fallbackSlotLtSeven)
        (retainedDirectSourceFanEscapeAt_translate_angular_linear_lower
          kind index directSlot fallbackTerminal.1 directionsLt
          directSlotPositive offset)).symm

/-- A translated custom direct escape strictly avoids a delayed-lane fallback
radial route under strict compatible angular order. -/
theorem
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_escapedRadial_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (offset : Cell)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index directSlot).route)
      (retainedTerminalFanOuterEscapedRadialRoute
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        fallbackTerminal fallbackSlot) := by
  rcases angularOrder with
      ⟨slotsLt, directionsLt⟩ |
      ⟨slotsLt, directionsLt⟩
  · have directSlotLtSeven : directSlot.val < 7 := by
      have fallbackSlotLtEight := fallbackSlot.isLt
      omega
    have fallbackSlotPositive : 0 < fallbackSlot.val := by
      omega
    exact
      routesStrictlyAvoidEachOther_of_linear_separated
        (retainedTerminalFanOuterRadialSeparatorNormal
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.1)
        (Cell.linearValue
            (retainedTerminalFanOuterRadialSeparatorNormal
              (retainedDirectSourceFanTerminalAt kind index).1
              fallbackTerminal.1)
            (Cell.add offset
              (retainedDirectSourceFanCenterAt kind index)) +
          retainedTerminalFanOuterRadialSeparatorBound
            (retainedDirectSourceFanTerminalAt kind index).1
            fallbackTerminal.1)
        (retainedDirectSourceFanEscapeAt_translate_angular_linear_upper
          kind index directSlot fallbackTerminal.1 directionsLt
          directSlotLtSeven offset)
        (retainedTerminalFanOuterEscapedRadialRoute_linear_lower
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index))
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.1 fallbackTerminal.2 fallbackSlot
          directionsLt fallbackLengthPositive fallbackSlotPositive
          fallbackEscapeFits)
  · have fallbackSlotLtSeven : fallbackSlot.val < 7 := by
      have directSlotLtEight := directSlot.isLt
      omega
    have directSlotPositive : 0 < directSlot.val := by
      omega
    exact
      (routesStrictlyAvoidEachOther_of_linear_separated
        (retainedTerminalFanOuterRadialSeparatorNormal
          fallbackTerminal.1
          (retainedDirectSourceFanTerminalAt kind index).1)
        (Cell.linearValue
            (retainedTerminalFanOuterRadialSeparatorNormal
              fallbackTerminal.1
              (retainedDirectSourceFanTerminalAt kind index).1)
            (Cell.add offset
              (retainedDirectSourceFanCenterAt kind index)) +
          retainedTerminalFanOuterRadialSeparatorBound
            fallbackTerminal.1
            (retainedDirectSourceFanTerminalAt kind index).1)
        (retainedTerminalFanOuterEscapedRadialRoute_linear_upper
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index))
          fallbackTerminal.1
          (retainedDirectSourceFanTerminalAt kind index).1
          fallbackTerminal.2 fallbackSlot directionsLt
          fallbackLengthPositive fallbackSlotLtSeven
          fallbackEscapeFits)
        (retainedDirectSourceFanEscapeAt_translate_angular_linear_lower
          kind index directSlot fallbackTerminal.1 directionsLt
          directSlotPositive offset)).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
