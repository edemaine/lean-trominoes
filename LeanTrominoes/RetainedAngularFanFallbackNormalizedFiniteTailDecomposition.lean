/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureRightLocalization
import LeanTrominoes.RetainedAngularFanFallbackNormalizedFiniteTailData
import LeanTrominoes.RetainedAngularFanFallbackNormalizedSuffixDirectionData

/-! # Localizing fallback-suffix normalization to its finite tail -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Dynamic radial portion selected by the ordinary or escaped fallback
policy. -/
def RetainedFallbackFanKind.radialRouteAt
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  match kind with
  | .ordinary =>
      retainedTerminalFanOuterRadialRoute center terminal slot
  | .escaped =>
      retainedTerminalFanOuterEscapedRadialRoute center terminal slot

/-- Every selected radial portion starts at the source gate. -/
theorem RetainedFallbackFanKind.radialRouteAt_head?
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (kind.radialRouteAt center terminal slot).head? =
      some
        (retainedAngularFanOuterDemand
          center terminal slot).gate := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterRadialRoute_head?
        center terminal slot
  | escaped =>
      exact retainedTerminalFanOuterEscapedRadialRoute_head?
        center terminal slot

/-- Hence every selected radial portion is nonempty. -/
theorem RetainedFallbackFanKind.radialRouteAt_ne_nil
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    kind.radialRouteAt center terminal slot ≠ [] := by
  intro empty
  have head := kind.radialRouteAt_head?
    center terminal slot
  rw [empty] at head
  simp at head

/-- A positive valid radial portion ends at the finite local adapter's lane
port. -/
theorem RetainedFallbackFanKind.radialRouteAt_getLast?
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    (kind.radialRouteAt center terminal slot).getLast? =
      some
        (retainedTerminalFanOuterLanePort
          center terminal.1 slot) := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterRadialRoute_getLast?
        center terminal slot lengthPositive
  | escaped =>
      exact retainedTerminalFanOuterEscapedRadialRoute_getLast?
        center terminal slot lengthPositive valid

/-- Every positive valid selected radial portion is orthogonal. -/
theorem RetainedFallbackFanKind.radialRouteAt_orthogonal
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (kind.radialRouteAt center terminal slot) := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterRadialRoute_orthogonal
        center terminal slot
  | escaped =>
      exact retainedTerminalFanOuterEscapedRadialRoute_orthogonal
        center terminal slot

/-- The fixed tail starts at the radial route's lane port. -/
theorem retainedFallbackFanFiniteTailRouteAt_head?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedFallbackFanFiniteTailRouteAt
      center direction slot).head? =
        some
          (retainedTerminalFanOuterLanePort
            center direction slot) := by
  unfold retainedFallbackFanFiniteTailRouteAt
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterLocalRouteAt_head?
      center direction slot)

/-- The raw complete suffix is its policy-selected dynamic radial route
joined to the common fixed local-and-spoke tail. -/
theorem retainedFallbackFanSuffixRouteAt_eq_radial_join_finiteTail
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedFallbackFanSuffixRouteAt
        kind center terminal slot =
      joinAtEndpoint
        (kind.radialRouteAt center terminal slot)
        (retainedFallbackFanFiniteTailRouteAt
          center terminal.1 slot) := by
  have localNonempty :
      retainedTerminalFanOuterLocalRouteAt
          center terminal.1 slot ≠ [] := by
    intro empty
    have head := retainedTerminalFanOuterLocalRouteAt_head?
      center terminal.1 slot
    rw [empty] at head
    simp at head
  cases kind with
  | ordinary =>
      unfold retainedFallbackFanSuffixRouteAt
        RetainedFallbackFanKind.outerRouteAt
        RetainedFallbackFanKind.radialRouteAt
        retainedTerminalFanOuterCompleteRoute
        retainedFallbackFanFiniteTailRouteAt
      exact (joinAtEndpoint_assoc_of_middle_ne_nil
        localNonempty).symm
  | escaped =>
      unfold retainedFallbackFanSuffixRouteAt
        RetainedFallbackFanKind.outerRouteAt
        RetainedFallbackFanKind.radialRouteAt
        retainedTerminalFanOuterEscapedCompleteRoute
        retainedFallbackFanFiniteTailRouteAt
      exact (joinAtEndpoint_assoc_of_middle_ne_nil
        localNonempty).symm

/-- Whole-suffix normalization is unchanged when its nonsimple but fixed
local-and-spoke tail is normalized first. -/
theorem retainedFallbackFanSuffixRouteAt_normalize_finiteTail_right
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          kind center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint
          (kind.radialRouteAt center terminal slot)
          (AxisDirection.normalizeOrthogonalPolyline
            (retainedFallbackFanFiniteTailRouteAt
              center terminal.1 slot))) := by
  rw [retainedFallbackFanSuffixRouteAt_eq_radial_join_finiteTail]
  exact
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
      (kind.radialRouteAt_ne_nil center terminal slot)
      (retainedFallbackFanFiniteTailRouteAt_ne_nil
        center terminal.1 slot)
      (kind.radialRouteAt_orthogonal center terminal slot)
      (retainedFallbackFanFiniteTailRouteAt_orthogonal
        center terminal.1 slot)
      (kind.radialRouteAt_getLast?
        center terminal slot lengthPositive valid)
      (retainedFallbackFanFiniteTailRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
