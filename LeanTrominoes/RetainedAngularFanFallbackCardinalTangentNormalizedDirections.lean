/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureJoinPrefix
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateSuffixSeparation
import LeanTrominoes.RetainedAngularFanFallbackRouteLocalizedNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackRouteSimplicity
import LeanTrominoes.RetainedAngularFanFallbackSourceSuffixSeparation

/-! # Normalized fallbacks with a cardinal tangential gate entrance -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A simple source route whose last retained segment approaches a cardinal
ordinary fan gate opposite to its clockwise lane direction has the canonical
prefix-plus-normalized-suffix direction word. -/
theorem scaledSplicedOwnFigure7Route_cardinalTangent_normalized_directions
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
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline factor route)
            (scaleRetainedTerminalData factor terminal) slot)) =
      Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route)) ++
        retainedNormalizedFallbackFanSuffixDirections
          .ordinary (scaleRetainedTerminalData factor terminal) slot := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let sourcePrefix := retainedFallbackSourcePrefix scaledRoute
  let center := retainedFallbackFanCenter scaledRoute
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center scaledTerminal slot
  let gate :=
    (retainedAngularFanOuterDemand center scaledTerminal slot).gate
  let tangent := retainedTerminalFanCardinalBackwardTangentRoute
    center port scaledLength slot distance
  have routeLengthTwo : 2 ≤ route.length := by omega
  have scaledRouteLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLengthTwo
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledSimple : LocalIncidenceDrawing.RouteIsSimple scaledRoute :=
    routeIsSimple_scalePolyline
      (by exact_mod_cast factorPositive) routeSimple
  have scaledOrthogonal : OrthogonalPolyline scaledRoute :=
    routeOrthogonal.scalePolyline
      (by exact_mod_cast factorPositive)
  have scaledTerminalPositive : 0 < scaledTerminal.2 := by
    change 0 < (scaleRetainedTerminalData factor terminal).2
    rw [scaleRetainedTerminalData_length]
    exact Nat.mul_pos factorPositive terminalLengthPositive
  have sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple sourcePrefix := by
    exact retainedFallbackSourcePrefix_isSimple scaledRoute scaledSimple
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact
      (scaledOrthogonal.scalePolyline (by native_decide)).dropLast
  have leadingOrthogonal : OrthogonalPolyline sourcePrefix.dropLast :=
    sourcePrefixOrthogonal.dropLast
  have suffixOrthogonal : OrthogonalPolyline suffix := by
    exact retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center scaledTerminal slot scaledTerminalPositive trivial
  have leadingStrict :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        sourcePrefix.dropLast suffix := by
    simpa [scaledRoute, scaledTerminal, sourcePrefix, center, suffix] using
      retainedFallbackSourcePrefix_dropLast_strictlyAvoids_suffix
        RetainedFallbackFanKind.ordinary route terminal slot
        routeLengthTwo classified factorPositive clearance
        routeSimple routeOrthogonal trivial
  have scaledRouteLengthThree : 3 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using (show 2 ≤ scaledRoute.length - 1 by omega)
  have leadingLength : 0 < sourcePrefix.dropLast.length := by
    rw [List.length_dropLast]
    omega
  have leadingNonempty : sourcePrefix.dropLast ≠ [] :=
    List.ne_nil_of_length_pos leadingLength
  have gateEq :
      gate =
        (retainedAngularFanOuterDemand
          center (.compass port, scaledLength) slot).gate := by
    simpa [gate, scaledTerminal] using congrArg
      (fun data : RetainedTerminalData =>
        (retainedAngularFanOuterDemand center data slot).gate)
      scaledTerminalEq
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate, scaledRoute,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        scaledRoute scaledTerminal slot scaledRouteLength scaledClassified
  have leadingLast :
      sourcePrefix.dropLast.getLast? = tangent.head? := by
    rw [show tangent.head? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              center (.compass port, scaledLength) slot).gate
            (Cell.scale (-(distance : Int))
              (retainedTerminalFanOuterLaneStep
                (.compass port)))) by
      simp [tangent,
        retainedTerminalFanCardinalBackwardTangentRoute]]
    simpa [sourcePrefix, center, scaledRoute] using predecessor
  have tangentHead :
      tangent.head? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              center (.compass port, scaledLength) slot).gate
            (Cell.scale (-(distance : Int))
              (retainedTerminalFanOuterLaneStep
                (.compass port)))) := by
    simp [tangent, retainedTerminalFanCardinalBackwardTangentRoute]
  have prefixSplit :
      sourcePrefix = joinAtEndpoint sourcePrefix.dropLast tangent := by
    calc
      sourcePrefix = sourcePrefix.dropLast ++ [gate] :=
        (List.dropLast_append_getLast? gate sourcePrefixLast).symm
      _ = joinAtEndpoint sourcePrefix.dropLast tangent := by
        simp [joinAtEndpoint, tangent,
          retainedTerminalFanCardinalBackwardTangentRoute, gateEq]
  have tangentSuffixOnlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline tangent →
        point ∈ AxisDirection.unitSubdividePolyline suffix →
        point = gate := by
    intro point tangentMember suffixMember
    change point ∈ AxisDirection.unitSubdividePolyline
      (retainedFallbackFanSuffixRouteAt
        .ordinary center scaledTerminal slot) at suffixMember
    rw [show scaledTerminal = (.compass port, scaledLength) by
      simpa [scaledTerminal] using scaledTerminalEq] at suffixMember
    rw [gateEq]
    exact
      retainedTerminalFanCardinalBackwardTangentRoute_only_common_suffix
        center port scaledLength slot distance cardinal
        scaledLengthLarge distancePositive point tangentMember suffixMember
  have onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline sourcePrefix →
        point ∈ AxisDirection.unitSubdividePolyline suffix →
        point = gate := by
    intro point prefixMember suffixMember
    rw [prefixSplit] at prefixMember
    exact AxisDirection.unitSubdividePolyline_only_common_of_join_left_strict
      leadingNonempty leadingLast tangentHead leadingOrthogonal
      suffixOrthogonal leadingStrict tangentSuffixOnlyCommon
      point prefixMember suffixMember
  exact RetainedFallbackFanKind.splicedOwnFigure7Route_localized_normalized_directions
      .ordinary
      scaledRoute scaledTerminal slot scaledRouteLength scaledClassified
      scaledOrthogonal scaledTerminalPositive trivial sourcePrefixSimple
      (by simpa [sourcePrefix, suffix, center, gate] using onlyCommon)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
