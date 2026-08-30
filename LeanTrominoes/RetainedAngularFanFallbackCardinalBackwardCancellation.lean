/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationPolyline
import LeanTrominoes.RetainedAngularFanFallbackCardinalTangentNormalizedDirections

/-! # Bounded cancellation at a backward-cardinal fan junction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A backward-cardinal tangent introduces no immediate reversal, so the
bounded junction canceller preserves its prefix-plus-suffix word. -/
theorem boundedCancellation_backwardCardinalFallback
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (port : Port)
    (scaledLength distance : Nat)
    (factorPositive : 0 < factor)
    (clearance :
      288 < retainedTerminalFanTotalRefinement * factor)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeSimple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeOrthogonal : OrthogonalPolyline route)
    (terminalLengthPositive : 0 < terminal.2)
    (scaledTerminalEq :
      scaleRetainedTerminalData factor terminal =
        (.compass port, scaledLength))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (scaledLengthLarge : 2 ≤ scaledLength)
    (distancePositive : 0 < distance)
    (predecessor :
      (retainedFallbackSourcePrefix
        (scalePolyline factor route)).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter
                (scalePolyline factor route))
              (.compass port, scaledLength) slot).gate
            (Cell.scale (-(distance : Int))
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    BoundedDelimitedDirectionCancellation.output
        (DelimitedRouteJoin.delimited
          (Gadget.unitSubdivisionDirections
              (retainedFallbackSourcePrefix
                (scalePolyline factor route)) ++
            retainedNormalizedFallbackFanSuffixDirections
              .ordinary
              (scaleRetainedTerminalData factor terminal) slot)) =
      DelimitedRouteJoin.delimited
        (Gadget.unitSubdivisionDirections
            (retainedFallbackSourcePrefix
              (scalePolyline factor route)) ++
          retainedNormalizedFallbackFanSuffixDirections
            .ordinary
            (scaleRetainedTerminalData factor terminal) slot) := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let sourcePrefix := retainedFallbackSourcePrefix scaledRoute
  let center := retainedFallbackFanCenter scaledRoute
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center scaledTerminal slot
  let gate :=
    (retainedAngularFanOuterDemand center scaledTerminal slot).gate
  let spliced := RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
    scaledRoute scaledTerminal slot
  have routeLengthTwo : 2 ≤ route.length := by omega
  have scaledRouteLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLengthTwo
  have scaledRouteLengthThree : 3 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledOrthogonal : OrthogonalPolyline scaledRoute :=
    routeOrthogonal.scalePolyline
      (by exact_mod_cast factorPositive)
  have scaledTerminalPositive : 0 < scaledTerminal.2 := by
    change 0 < (scaleRetainedTerminalData factor terminal).2
    rw [scaleRetainedTerminalData_length]
    exact Nat.mul_pos factorPositive terminalLengthPositive
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix :=
    (scaledOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ scaledRoute.length - 1 by omega)
  have sourcePrefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center scaledTerminal slot scaledTerminalPositive trivial
  have suffixHead : suffix.head? = some gate := by
    simpa [suffix, gate] using retainedFallbackFanSuffixRouteAt_head?
      .ordinary center scaledTerminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    change suffix.head? = _ at suffixHead
    rw [empty] at suffixHead
    simp at suffixHead
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, scaledRoute,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter, gate] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        scaledRoute scaledTerminal slot scaledRouteLength scaledClassified
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint sourcePrefix suffix) :=
    sourcePrefixOrthogonal.joinAtEndpoint suffixOrthogonal
      sourcePrefixLast suffixHead
  have joinedNonempty : joinAtEndpoint sourcePrefix suffix ≠ [] := by
    intro empty
    unfold joinAtEndpoint at empty
    exact sourcePrefixNonempty (List.append_eq_nil_iff.mp empty).1
  have splicedEq : spliced = joinAtEndpoint sourcePrefix suffix := by
    simpa [spliced, scaledRoute, scaledTerminal, sourcePrefix,
      center, suffix] using
      RetainedFallbackFanKind.splicedOwnFigure7Route_eq_join
        .ordinary scaledRoute scaledTerminal slot scaledRouteLength
        scaledClassified scaledOrthogonal trivial
  have splicedOrthogonal : OrthogonalPolyline spliced := by
    rw [splicedEq]
    exact joinedOrthogonal
  have splicedNonempty : spliced ≠ [] := by
    rw [splicedEq]
    exact joinedNonempty
  have normalizedNoReversal :=
    BoundedDelimitedDirectionCancellation.unitSubdivisionDirections_hasNoImmediateReversal
      (AxisDirection.normalizeOrthogonalPolyline spliced)
      (AxisDirection.normalizeOrthogonalPolyline_orthogonal
        splicedNonempty splicedOrthogonal)
      (AxisDirection.normalizeOrthogonalPolyline_isSimple
        splicedNonempty splicedOrthogonal)
  have normalizedDirections :=
    scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
      route terminal slot port scaledLength distance factorPositive
      clearance routeLength classified routeSimple routeOrthogonal
      terminalLengthPositive scaledTerminalEq cardinal scaledLengthLarge
      distancePositive predecessor
  rw [show spliced =
      RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal) slot by rfl,
    normalizedDirections] at normalizedNoReversal
  exact
    BoundedDelimitedDirectionCancellation.output_delimited_eq_of_noImmediateReversal
      _ normalizedNoReversal

end PeriodicEightOccurrenceSplit
end LeanTrominoes
