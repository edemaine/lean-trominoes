/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackNormalizedFiniteTailDecomposition
import LeanTrominoes.RetainedAngularFanFallbackRadialSplitNormalization
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections

/-! # Ordinary fallback suffixes split at the normalized terminal tail -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- A terminal tail starts one primitive outside its selected lane port. -/
theorem retainedFallbackFanTerminalTailRouteAt_head?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedFallbackFanTerminalTailRouteAt
      center direction slot).head? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset direction slot)
              direction.primitive)) := by
  unfold retainedFallbackFanTerminalTailRouteAt
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterRadialFinalStubAt_head?
      center direction slot)

/-- Before normalization, splitting an ordinary suffix before its final
radial primitive preserves the complete unit-direction word. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_terminalSplit_directions
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackFanSuffixRouteAt
          .ordinary center terminal slot) =
      Gadget.unitSubdivisionDirections
        (joinAtEndpoint
          (retainedTerminalFanOuterRadialPrefix center terminal slot)
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) := by
  have radialPrefixNonempty :
      retainedTerminalFanOuterRadialPrefix center terminal slot ≠ [] := by
    intro empty
    have head := retainedTerminalFanOuterRadialPrefix_head?
      center terminal slot
    rw [empty] at head
    simp at head
  have finalStubNonempty :
      retainedTerminalFanOuterRadialFinalStubAt
          center terminal.1 slot ≠ [] := by
    intro empty
    have head := retainedTerminalFanOuterRadialFinalStubAt_head?
      center terminal.1 slot
    rw [empty] at head
    simp at head
  rw [retainedFallbackFanSuffixRouteAt_eq_radial_join_finiteTail]
  simp only [RetainedFallbackFanKind.radialRouteAt]
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
    · rw [retainedTerminalFanOuterRadialRoute_directions]
      unfold retainedFallbackFanTerminalTailRouteAt
      rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
      · rw [retainedTerminalFanOuterRadialPrefix_directions,
          retainedTerminalFanOuterRadialFinalStubAt_directions,
          radialCopies_eq_pred_append
            (retainedTerminalFanOuterRadialLength terminal)
            terminal.1 radialPositive]
        simp [List.append_assoc]
      · exact finalStubNonempty
      · rw [retainedTerminalFanOuterRadialFinalStubAt_getLast?,
          retainedFallbackFanFiniteTailRouteAt_head?]
    · exact radialPrefixNonempty
    · rw [retainedTerminalFanOuterRadialPrefix_getLast?
          center terminal slot radialPositive,
        retainedFallbackFanTerminalTailRouteAt_head?]
  · exact RetainedFallbackFanKind.radialRouteAt_ne_nil
      .ordinary center terminal slot
  · rw [retainedTerminalFanOuterRadialRoute_getLast?
        center terminal slot lengthPositive,
      retainedFallbackFanFiniteTailRouteAt_head?]

/-- The ordinary raw suffix and its terminal-split form have identical
normalization, including cardinal routes whose input polylines differ only
by a removed collinear subdivision vertex. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_normalize_terminalSplit
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterRadialPrefix center terminal slot)
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) := by
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center terminal slot
  let radialPrefix :=
    retainedTerminalFanOuterRadialPrefix center terminal slot
  let terminalTail :=
    retainedFallbackFanTerminalTailRouteAt
      center terminal.1 slot
  let splitSuffix := joinAtEndpoint radialPrefix terminalTail
  have suffixHead :
      suffix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedFallbackFanSuffixRouteAt_head?
      .ordinary center terminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    rw [empty] at suffixHead
    simp at suffixHead
  have radialPrefixHead :
      radialPrefix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedTerminalFanOuterRadialPrefix_head? center terminal slot
  have radialPrefixNonempty : radialPrefix ≠ [] := by
    intro empty
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  have splitSuffixHead :
      splitSuffix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate := by
    exact joinAtEndpoint_head? radialPrefixHead
  have splitSuffixNonempty : splitSuffix ≠ [] := by
    intro empty
    rw [empty] at splitSuffixHead
    simp at splitSuffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center terminal slot lengthPositive trivial
  have radialPrefixOrthogonal : OrthogonalPolyline radialPrefix :=
    retainedTerminalFanOuterRadialPrefix_orthogonal
      center terminal slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have splitSuffixOrthogonal : OrthogonalPolyline splitSuffix := by
    exact radialPrefixOrthogonal.joinAtEndpoint
      terminalTailOrthogonal
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center terminal slot radialPositive)
      (retainedFallbackFanTerminalTailRouteAt_head?
        center terminal.1 slot)
  apply
    AxisDirection.normalizeOrthogonalPolyline_eq_of_head?_eq_of_directions_eq
      suffixNonempty splitSuffixNonempty
      suffixOrthogonal splitSuffixOrthogonal
  · rw [suffixHead, splitSuffixHead]
  · exact retainedFallbackFanOrdinarySuffixRouteAt_terminalSplit_directions
      center terminal slot lengthPositive radialPositive

/-- Ordinary suffix normalization can therefore be performed by first
normalizing only the fixed terminal tail.  The unbounded exterior prefix is
left as a separate streaming boundary. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_normalize_terminalTail_right
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterRadialPrefix center terminal slot)
          (AxisDirection.normalizeOrthogonalPolyline
            (retainedFallbackFanTerminalTailRouteAt
              center terminal.1 slot))) := by
  rw [retainedFallbackFanOrdinarySuffixRouteAt_normalize_terminalSplit
    center terminal slot lengthPositive radialPositive]
  have radialPrefixHead :=
    retainedTerminalFanOuterRadialPrefix_head?
      center terminal slot
  have radialPrefixNonempty :
      retainedTerminalFanOuterRadialPrefix center terminal slot ≠ [] := by
    intro empty
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  exact
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
      radialPrefixNonempty
      (retainedFallbackFanTerminalTailRouteAt_ne_nil
        center terminal.1 slot)
      (retainedTerminalFanOuterRadialPrefix_orthogonal
        center terminal slot)
      (retainedFallbackFanTerminalTailRouteAt_orthogonal
        center terminal.1 slot)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center terminal slot radialPositive)
      (retainedFallbackFanTerminalTailRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
