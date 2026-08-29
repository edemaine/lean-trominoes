/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureRightLocalization
import LeanTrominoes.RetainedAngularFanFallbackNormalizedSuffixDirectionData

/-! # Normalized fallback routes with localized suffix loop erasure -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Loop erasure may change a fallback suffix internally, but it remains
local to that suffix.  Thus a simple separated source prefix can be emitted
unchanged, followed by the canonical normalized suffix word. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_localized_normalized_directions
    (kind : RetainedFallbackFanKind)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal : OrthogonalPolyline route)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal)
    (sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (retainedFallbackSourcePrefix route))
    (onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline
          (retainedFallbackSourcePrefix route) →
        point ∈ AxisDirection.unitSubdividePolyline
          (retainedFallbackFanSuffixRouteAt
            kind (retainedFallbackFanCenter route) terminal slot) →
        point =
          (retainedAngularFanOuterDemand
            (retainedFallbackFanCenter route) terminal slot).gate) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route route terminal slot)) =
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix route) ++
        retainedNormalizedFallbackFanSuffixDirections
          kind terminal slot := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let suffix :=
    retainedFallbackFanSuffixRouteAt kind center terminal slot
  let normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline suffix
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have sourcePrefixNonempty : sourcePrefix ≠ [] := by
    have scaledLength :
        2 ≤ (scalePolyline
          retainedTerminalFanTotalRefinement route).length := by
      simpa [scalePolyline] using routeLength
    have sourcePrefixLength : 0 < sourcePrefix.length := by
      dsimp [sourcePrefix, retainedFallbackSourcePrefix]
      rw [List.length_dropLast]
      omega
    exact List.ne_nil_of_length_pos sourcePrefixLength
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact
      (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route terminal slot routeLength classified
  have suffixHead : suffix.head? = some gate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind center terminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro suffixEmpty
    rw [suffixEmpty] at suffixHead
    simp at suffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      kind center terminal slot lengthPositive valid
  have normalizedSuffixNonempty : normalizedSuffix ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      suffixNonempty suffixOrthogonal
  have normalizedSuffixOrthogonal :
      OrthogonalPolyline normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      suffixNonempty suffixOrthogonal
  have normalizedSuffixSimple :
      LocalIncidenceDrawing.RouteIsSimple normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline_isSimple
      suffixNonempty suffixOrthogonal
  have normalizedSuffixHead : normalizedSuffix.head? = some gate := by
    simpa [normalizedSuffix] using
      (AxisDirection.normalizeOrthogonalPolyline_head?
        suffixNonempty suffixOrthogonal).trans suffixHead
  have normalizedSuffixUnitSubdivision :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        normalizedSuffix :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        suffixNonempty suffixOrthogonal)
  have normalizedOnlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline sourcePrefix →
        point ∈ AxisDirection.unitSubdividePolyline normalizedSuffix →
        point = gate := by
    intro point prefixMember normalizedMember
    apply onlyCommon point
    · simpa [sourcePrefix] using prefixMember
    · apply
        (AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
          suffixNonempty suffixOrthogonal).subset
      rw [normalizedSuffixUnitSubdivision] at normalizedMember
      simpa [normalizedSuffix] using normalizedMember
  have routeEq := kind.splicedOwnFigure7Route_eq_join
    route terminal slot routeLength classified routeOrthogonal valid
  have normalizeRight :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
      sourcePrefixNonempty suffixNonempty
      sourcePrefixOrthogonal suffixOrthogonal
      sourcePrefixLast suffixHead
  calc
    Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (kind.splicedOwnFigure7Route route terminal slot)) =
        Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint sourcePrefix suffix)) := by
      rw [routeEq]
    _ = Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint sourcePrefix normalizedSuffix)) := by
      rw [normalizeRight]
    _ = Gadget.unitSubdivisionDirections sourcePrefix ++
          Gadget.unitSubdivisionDirections normalizedSuffix :=
      Gadget.unitSubdivisionDirections_normalizeOrthogonalPolyline_joinAtEndpoint_of_simple
        sourcePrefixNonempty normalizedSuffixNonempty
        sourcePrefixOrthogonal normalizedSuffixOrthogonal
        sourcePrefixSimple normalizedSuffixSimple
        sourcePrefixLast normalizedSuffixHead normalizedOnlyCommon
    _ = Gadget.unitSubdivisionDirections sourcePrefix ++
          retainedNormalizedFallbackFanSuffixDirections
            kind terminal slot := by
      rw [retainedFallbackFanSuffixRouteAt_normalized_directions
        kind center terminal slot lengthPositive valid]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
