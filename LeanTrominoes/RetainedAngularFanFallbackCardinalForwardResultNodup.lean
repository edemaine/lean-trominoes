/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardRestSeparation
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardSourceSplit

/-! # Duplicate-freeness after forward-cardinal cancellation -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Unit points strictly before the shifted gate in the adjusted source are
disjoint from the normalized ordinary suffix strictly after that gate. -/
theorem retainedFallbackCardinalForwardLeadingPoints_disjoint_afterLaneRest
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
      RoutesStrictlyAvoidEachOther
        (retainedFallbackSourcePrefix route).dropLast
        (retainedFallbackFanSuffixRouteAt
          .ordinary
          (retainedFallbackFanCenter route)
          (.compass port, length) slot)) :
    List.Disjoint
      (retainedFallbackCardinalForwardLeadingPoints
        route port length slot distance)
      (retainedTerminalFanCardinalOrdinaryAfterLaneRest
        (retainedFallbackFanCenter route)
        port length slot) := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let sourceLeading := sourcePrefix.dropLast
  let center := retainedFallbackFanCenter route
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate := (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance
  let adjustedSource :=
    retainedFallbackCardinalForwardAdjustedSourceRoute
      route port length slot distance
  let leading := retainedFallbackCardinalForwardLeadingPoints
    route port length slot distance
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center terminal slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix :=
    (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourceLeadingOrthogonal : OrthogonalPolyline sourceLeading :=
    sourcePrefixOrthogonal.dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    have routeLengthTwo : 2 ≤ route.length := by omega
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ route.length - 1 by omega)
  have sourceLeadingLength : 0 < sourceLeading.length := by
    dsimp [sourceLeading]
    rw [List.length_dropLast]
    omega
  have sourceLeadingNonempty : sourceLeading ≠ [] :=
    List.ne_nil_of_length_pos sourceLeadingLength
  let predecessorPoint := Cell.add gate
    (Cell.scale distance
      (retainedTerminalFanOuterLaneStep terminal.1))
  have sourceLeadingLast : sourceLeading.getLast? =
      some predecessorPoint := by
    simpa [sourceLeading, sourcePrefix, center, terminal, gate,
      predecessorPoint] using predecessor
  have tangentLeadingHead : tangentLeading.head? =
      some predecessorPoint := by
    simp [tangentLeading, predecessorPoint, gate, terminal]
  have adjustedEq :
      adjustedSource = joinAtEndpoint sourceLeading tangentLeading := by
    rfl
  have adjustedSubdivision :
      AxisDirection.unitSubdividePolyline adjustedSource =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (AxisDirection.unitSubdividePolyline tangentLeading) := by
    rw [adjustedEq]
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      sourceLeadingNonempty sourceLeadingLast tangentLeadingHead
  have lengthPositive : 0 < length := by omega
  have radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [terminal, retainedTerminalFanOuterRadialLength,
        retainedTerminalFanTotalRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalInterfaceMultiplier] at lengthLarge ⊢ <;>
      omega
  have suffixHead := retainedFallbackFanSuffixRouteAt_head?
    .ordinary center terminal slot
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    change suffix.head? = _ at suffixHead
    rw [empty] at suffixHead
    simp at suffixHead
  have suffixOrthogonal : OrthogonalPolyline suffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      .ordinary center terminal slot lengthPositive trivial
  have sourceSuffixDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline sourceLeading)
        (AxisDirection.unitSubdividePolyline suffix) :=
    sourceStrict.unitSubdividePolyline_disjoint
      sourceLeadingOrthogonal suffixOrthogonal
  have normalizedSuffixSublist :
      (AxisDirection.normalizeOrthogonalPolyline suffix).Sublist
        (AxisDirection.unitSubdividePolyline suffix) :=
    AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      suffixNonempty suffixOrthogonal
  have normalizedSuffixEq :
      AxisDirection.normalizeOrthogonalPolyline suffix =
        (retainedTerminalFanCardinalForwardOverlapPath
          center port length slot).reverse ++ rest := by
    simpa [suffix, center, terminal, rest] using
      retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
        center port length slot lengthPositive radialPositive
  have sourceLeadingRestDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline sourceLeading) rest := by
    intro point sourceMember restMember
    apply sourceSuffixDisjoint sourceMember
    apply normalizedSuffixSublist.subset
    rw [normalizedSuffixEq, List.mem_append]
    exact Or.inr restMember
  have tangentLeadingRestDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline tangentLeading) rest := by
    simpa [tangentLeading, rest, center] using
      retainedTerminalFanCardinalForwardTangentLeadingRoute_unit_disjoint_afterLaneRest
        center port length slot distance cardinal lengthLarge shiftStrict
  intro point leadingMember restMember
  have adjustedMember :
      point ∈ AxisDirection.unitSubdividePolyline adjustedSource := by
    exact List.mem_of_mem_dropLast leadingMember
  rw [adjustedSubdivision] at adjustedMember
  rcases mem_joinAtEndpoint adjustedMember with
      sourceMember | tangentMember
  · exact sourceLeadingRestDisjoint sourceMember restMember
  · exact tangentLeadingRestDisjoint tangentMember restMember

/-- Removing the forward out-and-back overlap leaves a duplicate-free unit
route from the adjusted source through the remainder of the suffix. -/
theorem retainedFallbackCardinalForwardCancellationResult_nodup
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
      RoutesStrictlyAvoidEachOther
        (retainedFallbackSourcePrefix route).dropLast
        (retainedFallbackFanSuffixRouteAt
          .ordinary
          (retainedFallbackFanCenter route)
          (.compass port, length) slot)) :
    (retainedFallbackCardinalForwardLeadingPoints
          route port length slot distance ++
        (retainedTerminalFanCardinalForwardOverlapPath
          (retainedFallbackFanCenter route)
          port length slot).head
            (retainedTerminalFanCardinalForwardOverlapPath_ne_nil
              (retainedFallbackFanCenter route)
              port length slot) ::
        retainedTerminalFanCardinalOrdinaryAfterLaneRest
          (retainedFallbackFanCenter route)
          port length slot).Nodup := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let leading := retainedFallbackCardinalForwardLeadingPoints
    route port length slot distance
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
  have pathNonempty : path ≠ [] := by
    exact retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  let overlapHead := path.head pathNonempty
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
  have sourceNodup :
      (AxisDirection.unitSubdividePolyline sourcePrefix).Nodup :=
    AxisDirection.unitSubdividePolyline_nodup
      sourcePrefixOrthogonal sourcePrefixSimple
  have sourceSplit :
      AxisDirection.unitSubdividePolyline sourcePrefix =
        leading ++ path := by
    simpa [sourcePrefix, center, leading, path] using
      retainedFallbackSourcePrefix_unitSubdivide_eq_forwardLeading_append_overlap
        route port length slot distance routeLength classified
        routeOrthogonal cardinal shiftStrict predecessor
  rw [sourceSplit] at sourceNodup
  have leadingNodup : leading.Nodup :=
    (List.nodup_append'.mp sourceNodup).1
  have leadingPathDisjoint : List.Disjoint leading path :=
    (List.nodup_append'.mp sourceNodup).2.2
  have pathRestNodup : (path ++ rest).Nodup := by
    simpa [path, rest, center] using
      retainedTerminalFanCardinalForwardOverlapPath_append_rest_nodup
        center port length slot lengthPositive radialPositive
  have restNodup : rest.Nodup :=
    (List.nodup_append'.mp pathRestNodup).2.1
  have pathRestDisjoint : List.Disjoint path rest :=
    (List.nodup_append'.mp pathRestNodup).2.2
  have overlapHeadMember : overlapHead ∈ path :=
    List.head_mem pathNonempty
  have overlapHeadRestFresh : overlapHead ∉ rest := by
    intro restMember
    exact pathRestDisjoint overlapHeadMember restMember
  have headRestNodup : (overlapHead :: rest).Nodup :=
    List.nodup_cons.mpr ⟨overlapHeadRestFresh, restNodup⟩
  have leadingRestDisjoint : List.Disjoint leading rest := by
    simpa [leading, rest, center] using
      retainedFallbackCardinalForwardLeadingPoints_disjoint_afterLaneRest
        route port length slot distance routeLength classified
        routeOrthogonal cardinal lengthLarge shiftStrict predecessor
        sourceStrict
  have leadingHeadRestDisjoint :
      List.Disjoint leading (overlapHead :: rest) := by
    intro point leadingMember otherMember
    rcases List.mem_cons.mp otherMember with rfl | restMember
    · exact leadingPathDisjoint leadingMember overlapHeadMember
    · exact leadingRestDisjoint leadingMember restMember
  have resultNodup :
      (leading ++ overlapHead :: rest).Nodup := by
    rw [List.nodup_append']
    exact ⟨leadingNodup, headRestNodup, leadingHeadRestDisjoint⟩
  simpa [leading, path, rest, center, overlapHead] using resultNodup

end PeriodicEightOccurrenceSplit
end LeanTrominoes
