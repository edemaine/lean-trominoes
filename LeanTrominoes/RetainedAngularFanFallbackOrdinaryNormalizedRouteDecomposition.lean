/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackOrdinaryNormalizedDirections

/-! # Point-level decomposition of normalized ordinary fallback suffixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The normalized ordinary suffix is its unchanged duplicate-free exterior
radial prefix followed by the normalized finite terminal tail. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center terminal slot) =
      joinAtEndpoint
        (AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterRadialPrefix center terminal slot))
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) := by
  let radialPrefix :=
    retainedTerminalFanOuterRadialPrefix center terminal slot
  let terminalTail :=
    retainedFallbackFanTerminalTailRouteAt center terminal.1 slot
  let normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline terminalTail
  let radialBoundary := Cell.add center
    (Cell.add
      (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
      terminal.1.primitive)
  have radialPrefixHead :=
    retainedTerminalFanOuterRadialPrefix_head? center terminal slot
  have radialPrefixNonempty : radialPrefix ≠ [] := by
    intro empty
    change radialPrefix.head? = _ at radialPrefixHead
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  have radialPrefixOrthogonal : OrthogonalPolyline radialPrefix :=
    retainedTerminalFanOuterRadialPrefix_orthogonal
      center terminal slot
  have radialPrefixLast :
      radialPrefix.getLast? = some radialBoundary :=
    retainedTerminalFanOuterRadialPrefix_getLast?
      center terminal slot radialPositive
  have radialPrefixNodup :
      (AxisDirection.unitSubdividePolyline radialPrefix).Nodup :=
    FallbackSuffixDirectionCompiler.retainedTerminalFanOuterRadialPrefix_unitSubdivide_nodup
      center terminal slot
  have terminalTailNonempty : terminalTail ≠ [] :=
    retainedFallbackFanTerminalTailRouteAt_ne_nil
      center terminal.1 slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have normalizedTailNonempty : normalizedTail ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailOrthogonal : OrthogonalPolyline normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailSimple :
      LocalIncidenceDrawing.RouteIsSimple normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline_isSimple
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailHead :
      normalizedTail.head? = some radialBoundary := by
    simpa [normalizedTail, terminalTail] using
      (AxisDirection.normalizeOrthogonalPolyline_head?
        terminalTailNonempty terminalTailOrthogonal).trans
        (retainedFallbackFanTerminalTailRouteAt_head?
          center terminal.1 slot)
  have onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline radialPrefix →
        point ∈ AxisDirection.unitSubdividePolyline normalizedTail →
        point = radialBoundary :=
    retainedTerminalFanOuterRadialPrefix_normalizedTerminalTail_only_common
      center terminal slot radialPositive
  have localizedNormalization :
      AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint radialPrefix normalizedTail) =
        joinAtEndpoint
          (AxisDirection.normalizeOrthogonalPolyline radialPrefix)
          (AxisDirection.unitSubdividePolyline normalizedTail) :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
      radialPrefixNonempty normalizedTailNonempty
      radialPrefixOrthogonal normalizedTailOrthogonal
      normalizedTailSimple radialPrefixLast normalizedTailHead onlyCommon
  have radialPrefixNormalized :
      AxisDirection.normalizeOrthogonalPolyline radialPrefix =
        AxisDirection.unitSubdividePolyline radialPrefix := by
    rw [AxisDirection.normalizeOrthogonalPolyline_eq_listLoopErase
        radialPrefixNonempty radialPrefixOrthogonal,
      Computability.listLoopErase_eq_self_of_nodup radialPrefixNodup]
  have normalizedTailUnit :
      AxisDirection.unitSubdividePolyline normalizedTail = normalizedTail :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        terminalTailNonempty terminalTailOrthogonal)
  rw [retainedFallbackFanOrdinarySuffixRouteAt_normalize_terminalTail_right
    center terminal slot lengthPositive radialPositive,
    localizedNormalization, radialPrefixNormalized, normalizedTailUnit]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
