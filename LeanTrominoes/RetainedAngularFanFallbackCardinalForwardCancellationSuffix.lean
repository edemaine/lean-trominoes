/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationSource

/-! # Suffix words at a forward-cardinal cancellation junction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Direction word strictly after the reversed occurrence-lane overlap. -/
def retainedFallbackCardinalForwardRestDirections
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  Gadget.unitSubdivisionDirections
    (path.head
        (retainedTerminalFanCardinalForwardOverlapPath_ne_nil
          center port length slot) ::
      retainedTerminalFanCardinalOrdinaryAfterLaneRest
        center port length slot)

/-- The normalized suffix begins with the overlap word traversed in the
opposite direction and then continues with the retained suffix word. -/
theorem retainedFallbackCardinalForwardNormalizedSuffix_directions
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < length)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanSuffixRouteAt
            .ordinary center (.compass port, length) slot)) =
      List.replicate
          (retainedTerminalFanCardinalCancellationCount slot).val
          (retainedTerminalFanCardinalForwardDirection port).opposite ++
        retainedFallbackCardinalForwardRestDirections
          center port length slot := by
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center (.compass port, length) slot
  let normalizedSuffix := AxisDirection.normalizeOrthogonalPolyline suffix
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
  have suffixHead := retainedFallbackFanSuffixRouteAt_head?
    .ordinary center (.compass port, length) slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    change suffix.head? = _ at suffixHead
    rw [empty] at suffixHead
    simp at suffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center (.compass port, length) slot
      lengthPositive trivial
  have normalizedSuffixUnit :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        normalizedSuffix :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        suffixNonempty suffixOrthogonal)
  have normalizedSuffixSplit :
      normalizedSuffix = path.reverse ++ rest := by
    simpa [normalizedSuffix, suffix, path, rest] using
      retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
        center port length slot lengthPositive radialPositive
  have secondSubdivision :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        path.reverse ++ rest :=
    normalizedSuffixUnit.trans normalizedSuffixSplit
  have pathNonempty : path ≠ [] :=
    retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  have normalizedSuffixOrthogonal : OrthogonalPolyline normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      suffixNonempty suffixOrthogonal
  have split :=
    BoundedDelimitedDirectionCancellation.unitSubdivisionDirections_eq_reverse_path_append_rest
      normalizedSuffix path rest normalizedSuffixOrthogonal pathNonempty
      secondSubdivision
  have pathOrthogonal : OrthogonalPolyline path := by
    exact AxisDirection.unitSubdividePolyline_orthogonal
      (retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
        center port length slot)
  have overlapDirections :=
    retainedTerminalFanCardinalForwardOverlapPath_directions
      center port length slot cardinal
  rw [Gadget.unitSubdivisionDirections_reverse path pathOrthogonal,
    overlapDirections] at split
  simpa [suffix, normalizedSuffix, path, rest,
    Gadget.reverseDirections,
    retainedFallbackCardinalForwardRestDirections] using split

/-- Dropping the bounded reversed overlap leaves precisely the retained
suffix word. -/
theorem retainedFallbackCardinalForwardNormalizedSuffix_drop
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < length)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    (Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanSuffixRouteAt
            .ordinary center (.compass port, length) slot))).drop
        (retainedTerminalFanCardinalCancellationCount slot).val =
      retainedFallbackCardinalForwardRestDirections
        center port length slot := by
  rw [retainedFallbackCardinalForwardNormalizedSuffix_directions
    center port length slot lengthPositive radialPositive cardinal]
  simp

end PeriodicEightOccurrenceSplit
end LeanTrominoes
