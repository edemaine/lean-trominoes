/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteNormalizedSimpleJoinDirection
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition

/-! # Normalized direction words of decomposed fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Both fallback outer policies begin at the same source gate. -/
theorem RetainedFallbackFanKind.outerRouteAt_head?
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (kind.outerRouteAt center terminal slot).head? =
      some (retainedAngularFanOuterDemand center terminal slot).gate := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterCompleteRoute_head?
        center terminal slot
  | escaped =>
      exact retainedTerminalFanOuterEscapedCompleteRoute_head?
        center terminal slot

/-- Both valid fallback outer policies are orthogonal. -/
theorem RetainedFallbackFanKind.outerRouteAt_orthogonal
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    OrthogonalPolyline (kind.outerRouteAt center terminal slot) := by
  cases kind with
  | ordinary =>
      exact retainedTerminalFanOuterCompleteRoute_orthogonal
        center terminal slot lengthPositive
  | escaped =>
      exact retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
        center terminal slot lengthPositive valid

/-- A valid complete fallback fan suffix is orthogonal. -/
theorem retainedFallbackFanSuffixRouteAt_orthogonal
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    OrthogonalPolyline
      (retainedFallbackFanSuffixRouteAt
        kind center terminal slot) := by
  unfold retainedFallbackFanSuffixRouteAt
  exact
    (kind.outerRouteAt_orthogonal
      center terminal slot lengthPositive valid).joinAtEndpoint
      (retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot)
      (kind.outerRouteAt_getLast?
        center terminal slot lengthPositive valid)
      (retainedTerminalFanFigure7SpokeRouteAt_head? center slot)

/-- A complete fallback suffix begins at the deleted source endpoint gate. -/
theorem retainedFallbackFanSuffixRouteAt_head?
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedFallbackFanSuffixRouteAt
      kind center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  unfold retainedFallbackFanSuffixRouteAt
  exact joinAtEndpoint_head?
    (kind.outerRouteAt_head? center terminal slot)

/-- Once the established separation geometry proves that the simple source
prefix and simple fan suffix meet only at their gate, normalization preserves
the source-prefix word and appends the translation-free fallback suffix word.
No whole-route loop-erasure machine remains in this interface. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_normalized_directions
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
    (suffixSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (retainedFallbackFanSuffixRouteAt
          kind (retainedFallbackFanCenter route) terminal slot))
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
        retainedFallbackFanSuffixDirections kind terminal slot := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let suffix :=
    retainedFallbackFanSuffixRouteAt kind center terminal slot
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
  have routeEq := kind.splicedOwnFigure7Route_eq_join
    route terminal slot routeLength classified routeOrthogonal valid
  calc
    Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (kind.splicedOwnFigure7Route route terminal slot)) =
        Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint sourcePrefix suffix)) := by
      rw [routeEq]
    _ = Gadget.unitSubdivisionDirections sourcePrefix ++
          Gadget.unitSubdivisionDirections suffix :=
      Gadget.unitSubdivisionDirections_normalizeOrthogonalPolyline_joinAtEndpoint_of_simple
        sourcePrefixNonempty suffixNonempty
        sourcePrefixOrthogonal suffixOrthogonal
        sourcePrefixSimple suffixSimple
        sourcePrefixLast suffixHead
        (by simpa [sourcePrefix, suffix, center, gate] using onlyCommon)
    _ = Gadget.unitSubdivisionDirections sourcePrefix ++
          retainedFallbackFanSuffixDirections kind terminal slot := by
      rw [retainedFallbackFanSuffixRouteAt_directions]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
