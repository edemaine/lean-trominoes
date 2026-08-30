/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections
import LeanTrominoes.RetainedAngularFanSourceSpliceTranslation

/-! # Translation invariance of normalized complete fallback routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

set_option maxRecDepth 10000

/-- Translating a valid source route translates its complete ordinary or
escaped fallback splice, so its normalized direction word is unchanged. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_translate_normalized_directions
    (kind : RetainedFallbackFanKind)
    (offset : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route
            (translatePolyline offset route) terminal slot)) =
      Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route route terminal slot)) := by
  let translatedRoute := translatePolyline offset route
  let refinedOffset :=
    Cell.scale retainedTerminalFanTotalRefinement offset
  let sourcePrefix := retainedFallbackSourcePrefix route
  let translatedPrefix := retainedFallbackSourcePrefix translatedRoute
  let center := retainedFallbackFanCenter route
  let translatedCenter := retainedFallbackFanCenter translatedRoute
  let suffix := retainedFallbackFanSuffixRouteAt
    kind center terminal slot
  let translatedSuffix := retainedFallbackFanSuffixRouteAt
    kind translatedCenter terminal slot
  let fullRoute := kind.splicedOwnFigure7Route route terminal slot
  let translatedFullRoute :=
    kind.splicedOwnFigure7Route translatedRoute terminal slot
  have routeNonempty : route ≠ [] := by
    apply List.ne_nil_of_length_pos
    omega
  have translatedLength : 2 ≤ translatedRoute.length := by
    simpa [translatedRoute, translatePolyline] using routeLength
  have translatedClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector translatedRoute) =
        some terminal := by
    simpa [translatedRoute, routeTerminalVector_translatePolyline] using
      classified
  have translatedOrthogonal : OrthogonalPolyline translatedRoute := by
    simpa [translatedRoute] using routeOrthogonal.translate offset
  have sourcePrefixEq :
      translatedPrefix = translatePolyline refinedOffset sourcePrefix := by
    calc
      translatedPrefix =
          (scalePolyline retainedTerminalFanTotalRefinement
            translatedRoute).dropLast := rfl
      _ =
          (translatePolyline refinedOffset
            (scalePolyline retainedTerminalFanTotalRefinement
              route)).dropLast := by
        dsimp only [translatedRoute]
        rw [scalePolyline_translatePolyline']
      _ = translatePolyline refinedOffset sourcePrefix := by
        simp [sourcePrefix, retainedFallbackSourcePrefix,
          translatePolyline, List.map_dropLast]
  have centerEq :
      translatedCenter = Cell.add refinedOffset center := by
    dsimp only [translatedCenter, translatedRoute,
      retainedFallbackFanCenter]
    rw [
      translatePolyline_getLastD offset route routeNonempty]
    simp [refinedOffset, center, retainedFallbackFanCenter,
      Cell.scale_add]
  have suffixEq :
      translatedSuffix = translatePolyline refinedOffset suffix := by
    have translated := retainedFallbackFanSuffixRouteAt_translatePolyline
      kind refinedOffset center terminal slot
    dsimp only [translatedSuffix, suffix]
    rw [centerEq]
    exact translated.symm
  have baseEq :
      fullRoute = joinAtEndpoint sourcePrefix suffix := by
    simpa [fullRoute, sourcePrefix, center, suffix] using
      kind.splicedOwnFigure7Route_eq_join route terminal slot
        routeLength classified routeOrthogonal valid
  have translatedEq :
      translatedFullRoute =
        joinAtEndpoint translatedPrefix translatedSuffix := by
    simpa [translatedFullRoute, translatedPrefix,
      translatedCenter, translatedSuffix] using
      kind.splicedOwnFigure7Route_eq_join
        translatedRoute terminal slot translatedLength
        translatedClassified translatedOrthogonal valid
  have fullTranslate :
      translatedFullRoute =
        translatePolyline refinedOffset fullRoute := by
    calc
      translatedFullRoute =
          joinAtEndpoint translatedPrefix translatedSuffix := translatedEq
      _ = joinAtEndpoint
          (translatePolyline refinedOffset sourcePrefix)
          (translatePolyline refinedOffset suffix) := by
        rw [sourcePrefixEq, suffixEq]
      _ = translatePolyline refinedOffset
          (joinAtEndpoint sourcePrefix suffix) := by
        exact (translatePolyline_joinAtEndpoint
          refinedOffset sourcePrefix suffix).symm
      _ = translatePolyline refinedOffset fullRoute := by
        rw [baseEq]
  have sourcePrefixLength : 0 < sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 0 < route.length - 1 by omega)
  have sourcePrefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos sourcePrefixLength
  have fullNonempty : fullRoute ≠ [] := by
    rw [baseEq]
    intro empty
    unfold joinAtEndpoint at empty
    exact sourcePrefixNonempty (List.append_eq_nil_iff.mp empty).1
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have suffixOrthogonal : OrthogonalPolyline suffix := by
    exact retainedFallbackFanSuffixRouteAt_orthogonal
      kind center terminal slot terminalLengthPositive valid
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route terminal slot routeLength classified
  have suffixHead : suffix.head? = some gate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind center terminal slot
  have fullOrthogonal : OrthogonalPolyline fullRoute := by
    rw [baseEq]
    exact sourcePrefixOrthogonal.joinAtEndpoint
      suffixOrthogonal sourcePrefixLast suffixHead
  have normalizedTranslate :
      AxisDirection.normalizeOrthogonalPolyline
          (translatePolyline refinedOffset fullRoute) =
        translatePolyline refinedOffset
          (AxisDirection.normalizeOrthogonalPolyline fullRoute) := by
    simpa [translatePolyline] using
      AxisDirection.normalizeOrthogonalPolyline_map_add
        fullNonempty fullOrthogonal refinedOffset
  rw [show kind.splicedOwnFigure7Route translatedRoute terminal slot =
      translatedFullRoute by rfl,
    fullTranslate,
    normalizedTranslate,
    Gadget.unitSubdivisionDirections_translatePolyline]

/-- If the raw source route is translated before source-clearance scaling,
the scaled complete fallback still has the same normalized direction word. -/
theorem RetainedFallbackFanKind.scaledSplicedOwnFigure7Route_translate_normalized_directions
    {factor : Nat}
    (kind : RetainedFallbackFanKind)
    (offset : Cell)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (factorPositive : 0 < factor)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid
      (scaleRetainedTerminalData factor terminal)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route
            (scalePolyline factor (translatePolyline offset route))
            (scaleRetainedTerminalData factor terminal) slot)) =
      Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route
            (scalePolyline factor route)
            (scaleRetainedTerminalData factor terminal) slot)) := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledOrthogonal : OrthogonalPolyline scaledRoute := by
    exact routeOrthogonal.scalePolyline
      (by exact_mod_cast factorPositive)
  have scaledLengthPositive : 0 < scaledTerminal.2 := by
    change 0 < factor * terminal.2
    exact Nat.mul_pos factorPositive terminalLengthPositive
  have translated :=
    kind.splicedOwnFigure7Route_translate_normalized_directions
      (Cell.scale factor offset) scaledRoute scaledTerminal slot
      scaledLength scaledClassified scaledOrthogonal
      scaledLengthPositive valid
  rw [scalePolyline_translatePolyline']
  simpa [scaledRoute, scaledTerminal] using translated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
