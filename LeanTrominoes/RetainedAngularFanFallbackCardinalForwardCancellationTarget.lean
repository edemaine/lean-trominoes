/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationSemantics
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardResultNodup

/-! # Nonreversal of the forward-cardinal cancellation result -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- The source and suffix words retained after forward-cardinal overlap
cancellation form the direction word of a simple normalized route. -/
theorem retainedFallbackCardinalForwardTarget_noImmediateReversal
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (.compass port, length))
    (routeOrthogonal : OrthogonalPolyline route)
    (sourcePrefixSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (retainedFallbackSourcePrefix route))
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port)))))
    (sourceStrict :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        (retainedFallbackSourcePrefix route).dropLast
        (retainedFallbackFanSuffixRouteAt
          .ordinary (retainedFallbackFanCenter route)
          (.compass port, length) slot)) :
    BoundedDelimitedDirectionCancellation.HasNoImmediateReversal
      (retainedFallbackCardinalForwardKeptDirections
          route port length slot distance ++
        retainedFallbackCardinalForwardRestDirections
          (retainedFallbackFanCenter route) port length slot) := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center (.compass port, length) slot
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  let normalizedSuffix := AxisDirection.normalizeOrthogonalPolyline suffix
  let leading := retainedFallbackCardinalForwardLeadingPoints
    route port length slot distance
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
  have lengthPositive : 0 < length := by omega
  have radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length) := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [retainedTerminalFanOuterRadialLength,
        retainedTerminalFanTotalRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalInterfaceMultiplier] at lengthLarge ⊢ <;>
      omega
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix :=
    (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ route.length - 1 by omega)
  have sourcePrefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have suffixHead := retainedFallbackFanSuffixRouteAt_head?
    .ordinary center (.compass port, length) slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    change suffix.head? = _ at suffixHead
    rw [empty] at suffixHead
    simp at suffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center (.compass port, length) slot
      lengthPositive trivial
  have normalizedSuffixNonempty : normalizedSuffix ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      suffixNonempty suffixOrthogonal
  have normalizedSuffixOrthogonal : OrthogonalPolyline normalizedSuffix :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      suffixNonempty suffixOrthogonal
  have normalizedSuffixHead : normalizedSuffix.head? = some gate := by
    rw [AxisDirection.normalizeOrthogonalPolyline_head?
      suffixNonempty suffixOrthogonal, suffixHead]
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, retainedFallbackSourcePrefix,
      center, retainedFallbackFanCenter, gate] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route (.compass port, length) slot (by omega) classified
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint sourcePrefix normalizedSuffix) :=
    sourcePrefixOrthogonal.joinAtEndpoint normalizedSuffixOrthogonal
      sourcePrefixLast normalizedSuffixHead
  have joinedNonempty :
      joinAtEndpoint sourcePrefix normalizedSuffix ≠ [] := by
    intro empty
    unfold joinAtEndpoint at empty
    exact sourcePrefixNonempty (List.append_eq_nil_iff.mp empty).1
  have sourceSubdivision :
      AxisDirection.unitSubdividePolyline sourcePrefix =
        leading ++ path := by
    simpa [sourcePrefix, center, leading, path] using
      retainedFallbackSourcePrefix_unitSubdivide_eq_forwardLeading_append_overlap
        route port length slot distance routeLength classified
        routeOrthogonal cardinal shiftStrict predecessor
  have normalizedSuffixUnit :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        normalizedSuffix :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        suffixNonempty suffixOrthogonal)
  have normalizedSuffixSplit :
      normalizedSuffix = path.reverse ++ rest := by
    simpa [normalizedSuffix, suffix, center, path, rest] using
      retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
        center port length slot lengthPositive radialPositive
  have secondSubdivision :
      AxisDirection.unitSubdividePolyline normalizedSuffix =
        path.reverse ++ rest :=
    normalizedSuffixUnit.trans normalizedSuffixSplit
  have pathNonempty : path ≠ [] :=
    retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  have pathRestNodup : (path ++ rest).Nodup := by
    simpa [path, rest] using
      retainedTerminalFanCardinalForwardOverlapPath_append_rest_nodup
        center port length slot lengthPositive radialPositive
  have resultNodup :
      (leading ++ path.head pathNonempty :: rest).Nodup := by
    simpa [leading, path, rest, center] using
      retainedFallbackCardinalForwardCancellationResult_nodup
        route port length slot distance routeLength classified
        routeOrthogonal sourcePrefixSimple cardinal lengthLarge
        shiftStrict predecessor sourceStrict
  have normalizedEq :
      AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint sourcePrefix normalizedSuffix) =
        leading ++ path.head pathNonempty :: rest :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_unit_outAndBack
      sourcePrefix normalizedSuffix leading path rest
      sourcePrefixNonempty normalizedSuffixNonempty
      sourcePrefixOrthogonal normalizedSuffixOrthogonal pathNonempty
      sourceSubdivision secondSubdivision pathRestNodup resultNodup
  let resultRoute := leading ++ path.head pathNonempty :: rest
  have resultUnitSteps :
      resultRoute.IsChain AxisDirection.IsUnitAxisStep := by
    have normalizedUnitSteps :=
      AxisDirection.normalizeOrthogonalPolyline_unitSteps
        joinedNonempty joinedOrthogonal
    rw [normalizedEq] at normalizedUnitSteps
    simpa [resultRoute] using normalizedUnitSteps
  have resultPointNoReversal :=
    BoundedDelimitedDirectionCancellation.point_hasNoImmediateReversal_of_nodup_unitSteps
      resultRoute (by simpa [resultRoute] using resultNodup) resultUnitSteps
  have resultStepNoReversal :=
    BoundedDelimitedDirectionCancellation.routeStepDirections_hasNoImmediateReversal
      resultRoute resultPointNoReversal
  have resultNoReversal :
      BoundedDelimitedDirectionCancellation.HasNoImmediateReversal
        (Gadget.unitSubdivisionDirections resultRoute) := by
    rw [Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
      resultRoute resultUnitSteps]
    exact resultStepNoReversal
  let keptRoute := leading ++ [path.head pathNonempty]
  let afterRoute := path.head pathNonempty :: rest
  have keptRouteNonempty : keptRoute ≠ [] := by simp [keptRoute]
  have joinEq : joinAtEndpoint keptRoute afterRoute = resultRoute := by
    simp [keptRoute, afterRoute, resultRoute, joinAtEndpoint]
  have targetDirections :
      retainedFallbackCardinalForwardKeptDirections
          route port length slot distance ++
        retainedFallbackCardinalForwardRestDirections
          center port length slot =
      Gadget.unitSubdivisionDirections resultRoute := by
    change
      Gadget.unitSubdivisionDirections keptRoute ++
          Gadget.unitSubdivisionDirections afterRoute = _
    rw [← Gadget.unitSubdivisionDirections_joinAtEndpoint
      keptRouteNonempty (by simp [keptRoute, afterRoute]), joinEq]
  rw [targetDirections]
  exact resultNoReversal

end PeriodicEightOccurrenceSplit
end LeanTrominoes
