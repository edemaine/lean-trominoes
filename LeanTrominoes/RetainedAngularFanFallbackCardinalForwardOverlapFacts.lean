/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardSuffixSplit

/-! # Structural facts about forward-cardinal overlap paths -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- A cardinal forward overlap always contains its shifted-gate endpoint. -/
theorem retainedTerminalFanCardinalForwardOverlapPath_ne_nil
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanCardinalForwardOverlapPath
        center port length slot ≠ [] := by
  let overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot
  have overlapHead :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute_head?
      center port length slot
  have overlapRouteNonempty : overlapRoute ≠ [] := by
    intro empty
    change overlapRoute.head? = _ at overlapHead
    rw [empty] at overlapHead
    simp at overlapHead
  exact AxisDirection.unitSubdividePolyline_ne_nil
    overlapRouteNonempty

/-- A cardinal forward overlap is already an ordered unit-step path. -/
theorem retainedTerminalFanCardinalForwardOverlapPath_unitSteps
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanCardinalForwardOverlapPath
      center port length slot).IsChain AxisDirection.IsUnitAxisStep := by
  exact AxisDirection.unitSubdividePolyline_unitSteps
    (retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
      center port length slot)

/-- The overlap removes exactly one occurrence-lane displacement from each
side of the out-and-back route. -/
theorem retainedTerminalFanCardinalForwardOverlapPath_edgeCount
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    (retainedTerminalFanCardinalForwardOverlapPath
        center port length slot).length - 1 =
      retainedTerminalFanOuterLaneSpacing * slot.val := by
  let overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot
  let overlap := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  have overlapNonempty : overlap ≠ [] := by
    exact retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  have overlapUnitSteps : overlap.IsChain AxisDirection.IsUnitAxisStep := by
    exact retainedTerminalFanCardinalForwardOverlapPath_unitSteps
      center port length slot
  have directionsLength :
      (Gadget.unitSubdivisionDirections overlap).length =
        overlap.length - 1 := by
    obtain ⟨head, tail, overlapEq⟩ :=
      List.exists_cons_of_ne_nil overlapNonempty
    have overlapUnitSteps' :
        (head :: tail).IsChain AxisDirection.IsUnitAxisStep := by
      simpa [overlapEq] using overlapUnitSteps
    rw [overlapEq,
      Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
        (head :: tail) overlapUnitSteps',
      Gadget.routeStepDirections_length]
    simp
  have directionsEq :
      Gadget.unitSubdivisionDirections overlap =
        Gadget.unitSubdivisionDirections overlapRoute := by
    exact Gadget.unitSubdivisionDirections_unitSubdividePolyline
      overlapRoute
      (retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
        center port length slot)
  rw [← directionsLength, directionsEq]
  rcases center with ⟨centerX, centerY⟩
  by_cases slotZero : slot.val = 0 <;>
    rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [overlapRoute,
      retainedTerminalFanCardinalForwardTangentOverlapRoute,
      retainedTerminalFanOuterLaneShiftRouteAt,
      retainedTerminalFanOuterLaneShiftRoute,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanOuterLaneSpacing,
      retainedAngularFanOuterDemand_gate_eq_interface_ray,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive, Port.unitVector,
      PeriodicOrthocrossing.translatePolyline,
      Gadget.unitSubdivisionDirections,
      AxisDirection.segmentLength, AxisDirection.between,
      Cell.add, Cell.scale, slotZero]
  all_goals
    rw [Int.natAbs_mul]
    norm_num

/-- Reversing the initial lane shift does not introduce contact with the
remainder of the normalized ordinary suffix. -/
theorem retainedTerminalFanCardinalForwardOverlapPath_append_rest_nodup
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < length)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length)) :
    (retainedTerminalFanCardinalForwardOverlapPath
        center port length slot ++
      retainedTerminalFanCardinalOrdinaryAfterLaneRest
        center port length slot).Nodup := by
  let suffix := retainedFallbackFanSuffixRouteAt
    .ordinary center (.compass port, length) slot
  let overlap := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
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
  have normalizedNodup :
      (AxisDirection.normalizeOrthogonalPolyline suffix).Nodup :=
    (AxisDirection.normalizeOrthogonalPolyline_isSimple
      suffixNonempty suffixOrthogonal).1
  have normalizedSplit :
      AxisDirection.normalizeOrthogonalPolyline suffix =
        overlap.reverse ++ rest := by
    simpa [suffix, overlap, rest] using
      retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
        center port length slot lengthPositive radialPositive
  rw [normalizedSplit] at normalizedNodup
  have reverseNodup : overlap.reverse.Nodup :=
    (List.nodup_append'.mp normalizedNodup).1
  have restNodup : rest.Nodup :=
    (List.nodup_append'.mp normalizedNodup).2.1
  have reverseDisjoint : List.Disjoint overlap.reverse rest :=
    (List.nodup_append'.mp normalizedNodup).2.2
  have overlapNodup : overlap.Nodup := by
    exact List.nodup_reverse.mp reverseNodup
  rw [List.nodup_append']
  refine ⟨overlapNodup, restNodup, ?_⟩
  intro point overlapMember restMember
  exact reverseDisjoint (by simpa using overlapMember) restMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
