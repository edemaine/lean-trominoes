/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineNormalizationDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections

/-! # Directional extensionality of normalized fallback splices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- For fixed terminal data, policy, and occurrence slot, the normalized
complete fallback word depends only on the source-prefix direction word. -/
theorem RetainedFallbackFanKind.splicedOwnFigure7Route_normalized_directions_eq_of_sourcePrefix_directions_eq
    (kind : RetainedFallbackFanKind)
    (first second : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector first) =
        some terminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector second) =
        some terminal)
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (terminalLengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal)
    (prefixDirectionsEq :
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix first) =
        Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix second)) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route first terminal slot)) =
      Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (kind.splicedOwnFigure7Route second terminal slot)) := by
  let firstPrefix := retainedFallbackSourcePrefix first
  let secondPrefix := retainedFallbackSourcePrefix second
  let firstCenter := retainedFallbackFanCenter first
  let secondCenter := retainedFallbackFanCenter second
  let firstSuffix :=
    retainedFallbackFanSuffixRouteAt
      kind firstCenter terminal slot
  let secondSuffix :=
    retainedFallbackFanSuffixRouteAt
      kind secondCenter terminal slot
  let firstFull := kind.splicedOwnFigure7Route first terminal slot
  let secondFull := kind.splicedOwnFigure7Route second terminal slot
  let firstGate :=
    (retainedAngularFanOuterDemand
      firstCenter terminal slot).gate
  let secondGate :=
    (retainedAngularFanOuterDemand
      secondCenter terminal slot).gate
  have firstPrefixLength : 0 < firstPrefix.length := by
    dsimp [firstPrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 0 < first.length - 1 by omega)
  have secondPrefixLength : 0 < secondPrefix.length := by
    dsimp [secondPrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 0 < second.length - 1 by omega)
  have firstPrefixNonempty : firstPrefix ≠ [] :=
    List.ne_nil_of_length_pos firstPrefixLength
  have secondPrefixNonempty : secondPrefix ≠ [] :=
    List.ne_nil_of_length_pos secondPrefixLength
  have firstPrefixOrthogonal : OrthogonalPolyline firstPrefix := by
    exact (firstOrthogonal.scalePolyline (by native_decide)).dropLast
  have secondPrefixOrthogonal : OrthogonalPolyline secondPrefix := by
    exact (secondOrthogonal.scalePolyline (by native_decide)).dropLast
  have firstSuffixOrthogonal : OrthogonalPolyline firstSuffix := by
    exact retainedFallbackFanSuffixRouteAt_orthogonal
      kind firstCenter terminal slot terminalLengthPositive valid
  have secondSuffixOrthogonal : OrthogonalPolyline secondSuffix := by
    exact retainedFallbackFanSuffixRouteAt_orthogonal
      kind secondCenter terminal slot terminalLengthPositive valid
  have firstPrefixLast : firstPrefix.getLast? = some firstGate := by
    simpa [firstPrefix, firstCenter, firstGate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        first terminal slot firstLength firstClassified
  have secondPrefixLast : secondPrefix.getLast? = some secondGate := by
    simpa [secondPrefix, secondCenter, secondGate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        second terminal slot secondLength secondClassified
  have firstSuffixHead : firstSuffix.head? = some firstGate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind firstCenter terminal slot
  have secondSuffixHead : secondSuffix.head? = some secondGate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind secondCenter terminal slot
  have firstFullEq :
      firstFull = joinAtEndpoint firstPrefix firstSuffix := by
    simpa [firstFull, firstPrefix, firstCenter, firstSuffix] using
      kind.splicedOwnFigure7Route_eq_join
        first terminal slot firstLength firstClassified
        firstOrthogonal valid
  have secondFullEq :
      secondFull = joinAtEndpoint secondPrefix secondSuffix := by
    simpa [secondFull, secondPrefix, secondCenter, secondSuffix] using
      kind.splicedOwnFigure7Route_eq_join
        second terminal slot secondLength secondClassified
        secondOrthogonal valid
  have firstFullNonempty : firstFull ≠ [] := by
    rw [firstFullEq]
    simp [joinAtEndpoint, firstPrefixNonempty]
  have secondFullNonempty : secondFull ≠ [] := by
    rw [secondFullEq]
    simp [joinAtEndpoint, secondPrefixNonempty]
  have firstFullOrthogonal : OrthogonalPolyline firstFull := by
    rw [firstFullEq]
    exact firstPrefixOrthogonal.joinAtEndpoint
      firstSuffixOrthogonal
      firstPrefixLast firstSuffixHead
  have secondFullOrthogonal : OrthogonalPolyline secondFull := by
    rw [secondFullEq]
    exact secondPrefixOrthogonal.joinAtEndpoint
      secondSuffixOrthogonal
      secondPrefixLast secondSuffixHead
  have fullDirectionsEq :
      Gadget.unitSubdivisionDirections firstFull =
        Gadget.unitSubdivisionDirections secondFull := by
    rw [firstFullEq, secondFullEq]
    calc
      Gadget.unitSubdivisionDirections
            (joinAtEndpoint firstPrefix firstSuffix) =
          Gadget.unitSubdivisionDirections firstPrefix ++
            Gadget.unitSubdivisionDirections firstSuffix :=
        Gadget.unitSubdivisionDirections_joinAtEndpoint
          firstPrefixNonempty
          (firstPrefixLast.trans firstSuffixHead.symm)
      _ = Gadget.unitSubdivisionDirections secondPrefix ++
            Gadget.unitSubdivisionDirections secondSuffix := by
        rw [retainedFallbackFanSuffixRouteAt_directions,
          retainedFallbackFanSuffixRouteAt_directions]
        exact congrArg
          (fun word => word ++
            retainedFallbackFanSuffixDirections kind terminal slot)
          prefixDirectionsEq
      _ = Gadget.unitSubdivisionDirections
            (joinAtEndpoint secondPrefix secondSuffix) :=
        (Gadget.unitSubdivisionDirections_joinAtEndpoint
          secondPrefixNonempty
          (secondPrefixLast.trans secondSuffixHead.symm)).symm
  simpa [firstFull, secondFull] using
    AxisDirection.unitSubdivisionDirections_normalizeOrthogonalPolyline_eq_of_directions_eq
      firstFullNonempty secondFullNonempty
      firstFullOrthogonal secondFullOrthogonal fullDirectionsEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
