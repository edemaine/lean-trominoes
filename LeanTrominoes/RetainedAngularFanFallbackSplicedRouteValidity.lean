/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections

/-! # Validity of complete retained fallback splices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- A valid retained fallback splice is nonempty and orthogonal before its
final loop-erasure normalization. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_valid
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
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    kind.splicedOwnFigure7Route route terminal slot ≠ [] ∧
      OrthogonalPolyline
        (kind.splicedOwnFigure7Route route terminal slot) := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let fanSuffix := retainedFallbackFanSuffixRouteAt
    kind center terminal slot
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have prefixLength : 0 < sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 0 < route.length - 1 by omega)
  have prefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos prefixLength
  have prefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have suffixOrthogonal : OrthogonalPolyline fanSuffix := by
    exact retainedFallbackFanSuffixRouteAt_orthogonal
      kind center terminal slot terminalLengthPositive valid
  have prefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate, retainedFallbackSourcePrefix,
      retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route terminal slot routeLength classified
  have suffixHead : fanSuffix.head? = some gate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind center terminal slot
  have fullEq :
      kind.splicedOwnFigure7Route route terminal slot =
        joinAtEndpoint sourcePrefix fanSuffix := by
    simpa [sourcePrefix, center, fanSuffix] using
      kind.splicedOwnFigure7Route_eq_join
        route terminal slot routeLength classified
        routeOrthogonal valid
  rw [fullEq]
  constructor
  · simp [joinAtEndpoint, prefixNonempty]
  · exact prefixOrthogonal.joinAtEndpoint
      suffixOrthogonal prefixLast suffixHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
