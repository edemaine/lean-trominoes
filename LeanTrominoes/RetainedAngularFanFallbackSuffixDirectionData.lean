/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.RetainedAngularFanOuterRouteTranslation
import LeanTrominoes.RetainedAngularFanSourceCompleteOwnCycleSeparation

/-! # Translation-free direction data for fallback retained-fan suffixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The two source-boundary policies used after a direct atlas lookup fails. -/
inductive RetainedFallbackFanKind
  | ordinary
  | escaped
  deriving DecidableEq, Fintype, Inhabited

/-- Select the ordinary or delayed-lane outer fan without changing its
common Figure 7 boundary endpoint. -/
def RetainedFallbackFanKind.outerRouteAt
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  match kind with
  | .ordinary =>
      retainedTerminalFanOuterCompleteRoute center terminal slot
  | .escaped =>
      retainedTerminalFanOuterEscapedCompleteRoute center terminal slot

/-- Complete fallback suffix from the deleted source endpoint gate through
the selected outer fan and the matching Figure 7 spoke. -/
def retainedFallbackFanSuffixRouteAt
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (kind.outerRouteAt center terminal slot)
    (retainedTerminalFanFigure7SpokeRouteAt center slot)

/-- Canonical translation-free direction word for one fallback suffix. -/
def retainedFallbackFanSuffixDirections
    (kind : RetainedFallbackFanKind)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (retainedFallbackFanSuffixRouteAt
      kind (0, 0) terminal slot)

/-- Translating the center translates the complete fallback suffix. -/
theorem retainedFallbackFanSuffixRouteAt_translatePolyline
    (kind : RetainedFallbackFanKind)
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedFallbackFanSuffixRouteAt
          kind center terminal slot) =
      retainedFallbackFanSuffixRouteAt
        kind (Cell.add offset center) terminal slot := by
  cases kind with
  | ordinary =>
      unfold retainedFallbackFanSuffixRouteAt
        RetainedFallbackFanKind.outerRouteAt
      rw [translatePolyline_joinAtEndpoint,
        retainedTerminalFanOuterCompleteRoute_translatePolyline]
      unfold retainedTerminalFanFigure7SpokeRouteAt
      rw [translatePolyline_add]
      congr 2
      rcases offset with ⟨offsetX, offsetY⟩
      rcases center with ⟨centerX, centerY⟩
      simp [Cell.add, add_comm]
  | escaped =>
      unfold retainedFallbackFanSuffixRouteAt
        RetainedFallbackFanKind.outerRouteAt
      rw [translatePolyline_joinAtEndpoint,
        retainedTerminalFanOuterEscapedCompleteRoute_translatePolyline]
      unfold retainedTerminalFanFigure7SpokeRouteAt
      rw [translatePolyline_add]
      congr 2
      rcases offset with ⟨offsetX, offsetY⟩
      rcases center with ⟨centerX, centerY⟩
      simp [Cell.add, add_comm]

/-- Absolute source coordinates disappear from the fallback suffix word. -/
theorem retainedFallbackFanSuffixRouteAt_directions
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackFanSuffixRouteAt
          kind center terminal slot) =
      retainedFallbackFanSuffixDirections kind terminal slot := by
  have translated :=
    retainedFallbackFanSuffixRouteAt_translatePolyline
      kind center (0, 0) terminal slot
  simp only [Cell.add_zero] at translated
  rw [← translated]
  exact Gadget.unitSubdivisionDirections_translatePolyline center _

/-- The only extra validity condition for the delayed-lane policy. -/
def RetainedFallbackFanKind.Valid
    (kind : RetainedFallbackFanKind)
    (terminal : RetainedTerminalData) : Prop :=
  match kind with
  | .ordinary => True
  | .escaped =>
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal

/-- Both policies reach the same positioned Figure 7 boundary. -/
theorem RetainedFallbackFanKind.outerRouteAt_getLast?
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    (kind.outerRouteAt center terminal slot).getLast? =
      some
        (Cell.add center
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val))) := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterCompleteRoute_getLast?
        center terminal slot lengthPositive
  | escaped =>
      exact retainedTerminalFanOuterEscapedCompleteRoute_getLast?
        center terminal slot lengthPositive valid

/-- The fallback suffix word splits into the selected outer-fan word and the
fixed Figure 7 spoke word. -/
theorem retainedFallbackFanSuffixDirections_eq
    (kind : RetainedFallbackFanKind)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    retainedFallbackFanSuffixDirections kind terminal slot =
      Gadget.unitSubdivisionDirections
          (kind.outerRouteAt (0, 0) terminal slot) ++
        Gadget.unitSubdivisionDirections
          (retainedTerminalFanFigure7SpokeRouteAt (0, 0) slot) := by
  unfold retainedFallbackFanSuffixDirections
    retainedFallbackFanSuffixRouteAt
  cases kind with
  | ordinary =>
      simp only [RetainedFallbackFanKind.outerRouteAt]
      apply Gadget.unitSubdivisionDirections_joinAtEndpoint
      · intro outerEmpty
        have outerHead :=
          retainedTerminalFanOuterCompleteRoute_head?
            (0, 0) terminal slot
        rw [outerEmpty] at outerHead
        simp at outerHead
      · rw [retainedTerminalFanOuterCompleteRoute_getLast?
          (0, 0) terminal slot lengthPositive,
          retainedTerminalFanFigure7SpokeRouteAt_head?]
  | escaped =>
      simp only [RetainedFallbackFanKind.outerRouteAt]
      apply Gadget.unitSubdivisionDirections_joinAtEndpoint
      · intro outerEmpty
        have outerHead :=
          retainedTerminalFanOuterEscapedCompleteRoute_head?
            (0, 0) terminal slot
        rw [outerEmpty] at outerHead
        simp at outerHead
      · rw [retainedTerminalFanOuterEscapedCompleteRoute_getLast?
          (0, 0) terminal slot lengthPositive valid,
          retainedTerminalFanFigure7SpokeRouteAt_head?]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
