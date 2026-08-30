/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureOutAndBack
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardResultNodup
import LeanTrominoes.RetainedAngularFanFallbackRouteSimplicity

/-! # Normalized fallbacks with a forward cardinal tangential entrance -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A simple source route approaching a cardinal ordinary fan gate in the
clockwise lane direction cancels the lane-shift overlap.  The normalized
word trims exactly that overlap from the source and suffix words. -/
theorem scaledSplicedOwnFigure7Route_forwardCardinalTangent_normalized_directions
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
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix
        (scalePolyline factor route)).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter
                (scalePolyline factor route))
              (.compass port, scaledLength) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
            (scalePolyline factor route)
            (scaleRetainedTerminalData factor terminal) slot)) =
      (Gadget.unitSubdivisionDirections
          (retainedFallbackSourcePrefix
            (scalePolyline factor route))).take
          ((Gadget.unitSubdivisionDirections
              (retainedFallbackSourcePrefix
                (scalePolyline factor route))).length -
            retainedTerminalFanOuterLaneSpacing * slot.val) ++
        (retainedNormalizedFallbackFanSuffixDirections
          .ordinary (scaleRetainedTerminalData factor terminal) slot).drop
            (retainedTerminalFanOuterLaneSpacing * slot.val) := by
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let sourcePrefix := retainedFallbackSourcePrefix scaledRoute
  let center := retainedFallbackFanCenter scaledRoute
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center scaledTerminal slot
  let normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline suffix
  let gate :=
    (retainedAngularFanOuterDemand center scaledTerminal slot).gate
  let leading := retainedFallbackCardinalForwardLeadingPoints
    scaledRoute port scaledLength slot distance
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port scaledLength slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port scaledLength slot
  have routeLengthTwo : 2 ≤ route.length := by omega
  have scaledRouteLengthTwo : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLengthTwo
  have scaledRouteLengthThree : 3 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified factorPositive classified
  have scaledTerminalPortEq :
      scaledTerminal = (.compass port, scaledLength) := by
    simpa [scaledTerminal] using scaledTerminalEq
  have scaledClassifiedPort :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some (.compass port, scaledLength) := by
    rw [scaledClassified, scaledTerminalPortEq]
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
  have scaledLengthPositive : 0 < scaledLength := by omega
  have radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, scaledLength) := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [retainedTerminalFanOuterRadialLength,
        retainedTerminalFanTotalRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalInterfaceMultiplier] at scaledLengthLarge ⊢ <;>
      omega
  have sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple sourcePrefix :=
    retainedFallbackSourcePrefix_isSimple scaledRoute scaledSimple
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix :=
    (scaledOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ scaledRoute.length - 1 by omega)
  have sourcePrefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have scaledGateEq :
      gate =
        (retainedAngularFanOuterDemand
          center (.compass port, scaledLength) slot).gate := by
    simpa [gate] using congrArg
      (fun data : RetainedTerminalData =>
        (retainedAngularFanOuterDemand center data slot).gate)
      scaledTerminalPortEq
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate, scaledRoute,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        scaledRoute scaledTerminal slot scaledRouteLengthTwo
        scaledClassified
  have suffixHead : suffix.head? = some gate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      .ordinary center scaledTerminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    rw [empty] at suffixHead
    simp at suffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center scaledTerminal slot scaledTerminalPositive trivial
  have normalizedSuffixNonempty : normalizedSuffix ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      suffixNonempty suffixOrthogonal
  have normalizedSuffixOrthogonal : OrthogonalPolyline normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      suffixNonempty suffixOrthogonal
  have normalizedSuffixHead : normalizedSuffix.head? = some gate := by
    simpa [normalizedSuffix] using
      (AxisDirection.normalizeOrthogonalPolyline_head?
        suffixNonempty suffixOrthogonal).trans suffixHead
  have normalizedSuffixUnit :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        normalizedSuffix :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        suffixNonempty suffixOrthogonal)
  have leadingStrict :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        sourcePrefix.dropLast suffix := by
    simpa [scaledRoute, scaledTerminal, sourcePrefix, center, suffix] using
      retainedFallbackSourcePrefix_dropLast_strictlyAvoids_suffix
        RetainedFallbackFanKind.ordinary route terminal slot
        routeLengthTwo classified factorPositive clearance
        routeSimple routeOrthogonal trivial
  have sourceSubdivision :
      AxisDirection.unitSubdividePolyline sourcePrefix =
        leading ++ path := by
    simpa [sourcePrefix, leading, path, center, scaledRoute] using
      retainedFallbackSourcePrefix_unitSubdivide_eq_forwardLeading_append_overlap
        scaledRoute port scaledLength slot distance
        scaledRouteLengthThree scaledClassifiedPort scaledOrthogonal
        cardinal shiftStrict
        (by simpa [scaledRoute, center] using predecessor)
  have normalizedSuffixSplit :
      normalizedSuffix = path.reverse ++ rest := by
    simpa [normalizedSuffix, suffix, path, rest, scaledTerminalPortEq] using
      retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
        center port scaledLength slot scaledLengthPositive radialPositive
  have secondSubdivision :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        path.reverse ++ rest :=
    normalizedSuffixUnit.trans normalizedSuffixSplit
  have pathNonempty : path ≠ [] := by
    exact retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port scaledLength slot
  have pathUnitSteps : path.IsChain AxisDirection.IsUnitAxisStep := by
    exact retainedTerminalFanCardinalForwardOverlapPath_unitSteps
      center port scaledLength slot
  have pathRestNodup : (path ++ rest).Nodup := by
    simpa [path, rest] using
      retainedTerminalFanCardinalForwardOverlapPath_append_rest_nodup
        center port scaledLength slot scaledLengthPositive radialPositive
  have resultNodup :
      (leading ++ path.head pathNonempty :: rest).Nodup := by
    simpa [leading, path, rest, center, scaledRoute] using
      retainedFallbackCardinalForwardCancellationResult_nodup
        scaledRoute port scaledLength slot distance
        scaledRouteLengthThree scaledClassifiedPort scaledOrthogonal
        sourcePrefixSimple cardinal scaledLengthLarge shiftStrict
        (by simpa [scaledRoute, center] using predecessor)
        (by simpa [sourcePrefix, suffix, center, scaledTerminalPortEq] using
          leadingStrict)
  have routeEq :=
    RetainedFallbackFanKind.splicedOwnFigure7Route_eq_join
      RetainedFallbackFanKind.ordinary
      scaledRoute scaledTerminal slot scaledRouteLengthTwo
      scaledClassified scaledOrthogonal trivial
  have normalizeRight :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_normalize_right
      sourcePrefixNonempty suffixNonempty
      sourcePrefixOrthogonal suffixOrthogonal
      sourcePrefixLast suffixHead
  have cancelled :=
    AxisDirection.unitSubdivisionDirections_normalize_joinAtEndpoint_of_unit_outAndBack
      sourcePrefix normalizedSuffix leading path rest
      sourcePrefixNonempty normalizedSuffixNonempty
      sourcePrefixOrthogonal normalizedSuffixOrthogonal
      pathNonempty pathUnitSteps sourceSubdivision secondSubdivision
      pathRestNodup resultNodup
  have pathEdgeCount :
      path.length - 1 =
        retainedTerminalFanOuterLaneSpacing * slot.val := by
    exact retainedTerminalFanCardinalForwardOverlapPath_edgeCount
      center port scaledLength slot cardinal
  have suffixDirections :
      Gadget.unitSubdivisionDirections normalizedSuffix =
        retainedNormalizedFallbackFanSuffixDirections
          .ordinary scaledTerminal slot := by
    simpa [normalizedSuffix, suffix] using
      retainedFallbackFanSuffixRouteAt_normalized_directions
        .ordinary center scaledTerminal slot scaledTerminalPositive trivial
  calc
    Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
              scaledRoute scaledTerminal slot)) =
        Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint sourcePrefix suffix)) := by
      rw [routeEq]
    _ = Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint sourcePrefix normalizedSuffix)) := by
      rw [normalizeRight]
    _ = (Gadget.unitSubdivisionDirections sourcePrefix).take
          ((Gadget.unitSubdivisionDirections sourcePrefix).length -
            (path.length - 1)) ++
        (Gadget.unitSubdivisionDirections normalizedSuffix).drop
          (path.length - 1) := cancelled
    _ = (Gadget.unitSubdivisionDirections sourcePrefix).take
          ((Gadget.unitSubdivisionDirections sourcePrefix).length -
            retainedTerminalFanOuterLaneSpacing * slot.val) ++
        (retainedNormalizedFallbackFanSuffixDirections
          .ordinary scaledTerminal slot).drop
            (retainedTerminalFanOuterLaneSpacing * slot.val) := by
      rw [pathEdgeCount, suffixDirections]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
