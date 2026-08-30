/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardTangentSplit
import LeanTrominoes.RetainedAngularFanFallbackOrdinaryNormalizedRouteDecomposition

/-! # Splitting normalized cardinal suffixes after their lane shift -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Unit path of the occurrence-lane shift traversed backward, from the
shifted gate to the source gate. -/
def retainedTerminalFanCardinalForwardOverlapPath
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot)

/-- Unit points of a normalized ordinary suffix strictly after its initial
occurrence-lane shift.  The shared shifted gate is omitted. -/
def retainedTerminalFanCardinalOrdinaryAfterLaneRest
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) : List Cell :=
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  (AxisDirection.unitSubdividePolyline
      ((retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
        shiftedGate)).tail ++
    (AxisDirection.normalizeOrthogonalPolyline
      (retainedFallbackFanTerminalTailRouteAt
        center terminal.1 slot)).tail

/-- The normalized ordinary suffix is the forward-overlap path traversed
back to the shifted gate, followed by the unit route strictly after that
gate. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq_overlap_reverse_append_rest
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < length)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (.compass port, length)) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center (.compass port, length) slot) =
      (retainedTerminalFanCardinalForwardOverlapPath
          center port length slot).reverse ++
        retainedTerminalFanCardinalOrdinaryAfterLaneRest
          center port length slot := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let laneRoute := retainedTerminalFanOuterLaneShiftRouteAt
    gate terminal.1 slot
  let inwardRoute :=
    (retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
      shiftedGate
  let radialPrefix :=
    retainedTerminalFanOuterRadialPrefix center terminal slot
  let terminalTail :=
    retainedFallbackFanTerminalTailRouteAt center terminal.1 slot
  let normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline terminalTail
  let overlapPath := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  have laneHead := retainedTerminalFanOuterLaneShiftRouteAt_head?
    gate terminal.1 slot
  have laneNonempty : laneRoute ≠ [] := by
    intro empty
    change laneRoute.head? = _ at laneHead
    rw [empty] at laneHead
    simp at laneHead
  have laneLast : laneRoute.getLast? = some shiftedGate := by
    simp [laneRoute, shiftedGate, terminal]
  have inwardHead : inwardRoute.head? = some shiftedGate := by
    exact RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardPrefixRay terminal) shiftedGate
  have radialSubdivision :
      AxisDirection.unitSubdividePolyline radialPrefix =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline laneRoute)
          (AxisDirection.unitSubdividePolyline inwardRoute) := by
    change AxisDirection.unitSubdividePolyline
        (joinAtEndpoint laneRoute inwardRoute) = _
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      laneNonempty laneLast inwardHead
  have laneOrthogonal : OrthogonalPolyline laneRoute :=
    retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      gate terminal.1 slot
  have overlapSubdivision :
      overlapPath =
        (AxisDirection.unitSubdividePolyline laneRoute).reverse := by
    unfold overlapPath retainedTerminalFanCardinalForwardOverlapPath
      retainedTerminalFanCardinalForwardTangentOverlapRoute
    change AxisDirection.unitSubdividePolyline laneRoute.reverse = _
    exact AxisDirection.unitSubdividePolyline_reverse
      laneRoute laneOrthogonal
  have normalizedDecomposition :=
    retainedFallbackFanOrdinarySuffixRouteAt_normalized_eq
      center terminal slot lengthPositive radialPositive
  change
    AxisDirection.normalizeOrthogonalPolyline
        (retainedFallbackFanSuffixRouteAt
          .ordinary center terminal slot) =
      overlapPath.reverse ++
        ((AxisDirection.unitSubdividePolyline inwardRoute).tail ++
          normalizedTail.tail)
  rw [normalizedDecomposition, radialSubdivision,
    overlapSubdivision, List.reverse_reverse]
  unfold joinAtEndpoint
  simp [normalizedTail, List.append_assoc]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
