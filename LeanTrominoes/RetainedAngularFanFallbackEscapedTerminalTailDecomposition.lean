/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackEscapedRadialPrefixEndpoint
import LeanTrominoes.RetainedAngularFanFallbackOrdinaryTerminalTailDecomposition

/-! # Escaped fallback suffixes split at the normalized terminal tail -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- Before normalization, splitting an escaped suffix before its final
radial primitive preserves the complete unit-direction word. -/
theorem retainedFallbackFanEscapedSuffixRouteAt_terminalSplit_directions
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackFanSuffixRouteAt
          .escaped center terminal slot) =
      Gadget.unitSubdivisionDirections
        (joinAtEndpoint
          (retainedTerminalFanOuterEscapedRadialPrefix
            center terminal slot)
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) := by
  have radialPrefixNonempty :
      retainedTerminalFanOuterEscapedRadialPrefix
          center terminal slot ≠ [] := by
    intro empty
    have head := retainedTerminalFanOuterEscapedRadialPrefix_head?
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
    · rw [retainedTerminalFanOuterEscapedRadialRoute_directions]
      unfold retainedFallbackFanTerminalTailRouteAt
      rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
      · rw [retainedTerminalFanOuterEscapedRadialPrefix_directions,
          retainedTerminalFanOuterRadialFinalStubAt_directions,
          radialCopies_eq_pred_append
            (retainedTerminalFanOuterRadialLength terminal -
              retainedTerminalFanOuterSourceEscapeLength)
            terminal.1 (by omega)]
        simp [List.append_assoc]
      · exact finalStubNonempty
      · rw [retainedTerminalFanOuterRadialFinalStubAt_getLast?,
          retainedFallbackFanFiniteTailRouteAt_head?]
    · exact radialPrefixNonempty
    · rw [retainedTerminalFanOuterEscapedRadialPrefix_getLast?
          center terminal slot escapeStrict,
        retainedFallbackFanTerminalTailRouteAt_head?]
  · exact RetainedFallbackFanKind.radialRouteAt_ne_nil
      .escaped center terminal slot
  · rw [retainedTerminalFanOuterEscapedRadialRoute_getLast?
        center terminal slot lengthPositive escapeStrict.le,
      retainedFallbackFanFiniteTailRouteAt_head?]

/-- The raw escaped suffix and its terminal-split form have identical
normalization. -/
theorem retainedFallbackFanEscapedSuffixRouteAt_normalize_terminalSplit
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .escaped center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterEscapedRadialPrefix
            center terminal slot)
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) := by
  let suffix := retainedFallbackFanSuffixRouteAt
    .escaped center terminal slot
  let radialPrefix :=
    retainedTerminalFanOuterEscapedRadialPrefix center terminal slot
  let terminalTail :=
    retainedFallbackFanTerminalTailRouteAt
      center terminal.1 slot
  let splitSuffix := joinAtEndpoint radialPrefix terminalTail
  have suffixHead :
      suffix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedFallbackFanSuffixRouteAt_head?
      .escaped center terminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    rw [empty] at suffixHead
    simp at suffixHead
  have radialPrefixHead :
      radialPrefix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedTerminalFanOuterEscapedRadialPrefix_head?
      center terminal slot
  have radialPrefixNonempty : radialPrefix ≠ [] := by
    intro empty
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  have splitSuffixHead :
      splitSuffix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    joinAtEndpoint_head? radialPrefixHead
  have splitSuffixNonempty : splitSuffix ≠ [] := by
    intro empty
    rw [empty] at splitSuffixHead
    simp at splitSuffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .escaped center terminal slot lengthPositive escapeStrict.le
  have radialPrefixOrthogonal : OrthogonalPolyline radialPrefix :=
    retainedTerminalFanOuterEscapedRadialPrefix_orthogonal
      center terminal slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have splitSuffixOrthogonal : OrthogonalPolyline splitSuffix :=
    radialPrefixOrthogonal.joinAtEndpoint
      terminalTailOrthogonal
      (retainedTerminalFanOuterEscapedRadialPrefix_getLast?
        center terminal slot escapeStrict)
      (retainedFallbackFanTerminalTailRouteAt_head?
        center terminal.1 slot)
  apply
    AxisDirection.normalizeOrthogonalPolyline_eq_of_head?_eq_of_directions_eq
      suffixNonempty splitSuffixNonempty
      suffixOrthogonal splitSuffixOrthogonal
  · rw [suffixHead, splitSuffixHead]
  · exact retainedFallbackFanEscapedSuffixRouteAt_terminalSplit_directions
      center terminal slot lengthPositive escapeStrict

/-- Escaped suffix normalization can first normalize only the fixed
terminal tail, leaving the exterior prefix as a streaming boundary. -/
theorem retainedFallbackFanEscapedSuffixRouteAt_normalize_terminalTail_right
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .escaped center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterEscapedRadialPrefix
            center terminal slot)
          (AxisDirection.normalizeOrthogonalPolyline
            (retainedFallbackFanTerminalTailRouteAt
              center terminal.1 slot))) := by
  rw [retainedFallbackFanEscapedSuffixRouteAt_normalize_terminalSplit
    center terminal slot lengthPositive escapeStrict]
  have radialPrefixHead :=
    retainedTerminalFanOuterEscapedRadialPrefix_head?
      center terminal slot
  have radialPrefixNonempty :
      retainedTerminalFanOuterEscapedRadialPrefix
          center terminal slot ≠ [] := by
    intro empty
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  exact
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
      radialPrefixNonempty
      (retainedFallbackFanTerminalTailRouteAt_ne_nil
        center terminal.1 slot)
      (retainedTerminalFanOuterEscapedRadialPrefix_orthogonal
        center terminal slot)
      (retainedFallbackFanTerminalTailRouteAt_orthogonal
        center terminal.1 slot)
      (retainedTerminalFanOuterEscapedRadialPrefix_getLast?
        center terminal slot escapeStrict)
      (retainedFallbackFanTerminalTailRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
