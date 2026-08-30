/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionReversal
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardTangentData

/-! # Splitting forward cardinal tangents at their shifted gate -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Portion of a forward tangent from its predecessor to the occurrence-
shifted gate. -/
def retainedTerminalFanCardinalForwardTangentLeadingRoute
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  [Cell.add gate
      (Cell.scale distance
        (retainedTerminalFanOuterLaneStep (.compass port))),
    Cell.add gate
      (retainedTerminalFanOuterLaneOffset (.compass port) slot)]

/-- The lane-shift overlap traversed backward from the shifted gate to the
source gate. -/
def retainedTerminalFanCardinalForwardTangentOverlapRoute
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  (retainedTerminalFanOuterLaneShiftRouteAt
    gate (.compass port) slot).reverse

/-- Insert the shifted gate into a forward tangent, exposing the exact
out-and-back overlap with the ordinary fan lane shift. -/
def retainedTerminalFanCardinalForwardTangentSplitRoute
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance)
    (retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot)

@[simp]
theorem retainedTerminalFanCardinalForwardTangentLeadingRoute_head?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) :
    (retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance).head? =
      some
        (Cell.add
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
  rfl

@[simp]
theorem retainedTerminalFanCardinalForwardTangentLeadingRoute_getLast?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) :
    (retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance).getLast? =
      some
        (Cell.add
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate
          (retainedTerminalFanOuterLaneOffset
            (.compass port) slot)) := by
  rfl

@[simp]
theorem retainedTerminalFanCardinalForwardTangentOverlapRoute_head?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot).head? =
      some
        (Cell.add
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate
          (retainedTerminalFanOuterLaneOffset
            (.compass port) slot)) := by
  unfold retainedTerminalFanCardinalForwardTangentOverlapRoute
  rw [List.head?_reverse,
    retainedTerminalFanOuterLaneShiftRouteAt_getLast?]

@[simp]
theorem retainedTerminalFanCardinalForwardTangentOverlapRoute_getLast?
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot).getLast? =
      some
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  unfold retainedTerminalFanCardinalForwardTangentOverlapRoute
  rw [List.getLast?_reverse,
    retainedTerminalFanOuterLaneShiftRouteAt_head?]

/-- The kept portion of a forward tangent is orthogonal whenever it extends
strictly beyond the shifted gate. -/
theorem retainedTerminalFanCardinalForwardTangentLeadingRoute_orthogonal
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance) :
    OrthogonalPolyline
      (retainedTerminalFanCardinalForwardTangentLeadingRoute
        center port length slot distance) := by
  rcases center with ⟨centerX, centerY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalFanCardinalForwardTangentLeadingRoute,
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
      OrthogonalPolyline, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      Cell.add, Cell.scale] at shiftStrict ⊢ <;>
    omega

/-- The reversed occurrence-lane overlap is orthogonal. -/
theorem retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedTerminalFanCardinalForwardTangentOverlapRoute
        center port length slot) := by
  unfold retainedTerminalFanCardinalForwardTangentOverlapRoute
  exact
    (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      (retainedAngularFanOuterDemand
        center (.compass port, length) slot).gate
      (.compass port) slot).reverse

/-- If the source tangent extends past the shifted gate, the split route is
orthogonal. -/
theorem retainedTerminalFanCardinalForwardTangentSplitRoute_orthogonal
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance) :
    OrthogonalPolyline
      (retainedTerminalFanCardinalForwardTangentSplitRoute
        center port length slot distance) := by
  rcases center with ⟨centerX, centerY⟩
  by_cases slotZero : slot.val = 0 <;>
    rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalFanCardinalForwardTangentSplitRoute,
      retainedTerminalFanCardinalForwardTangentLeadingRoute,
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
      translatePolyline, joinAtEndpoint,
      OrthogonalPolyline, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      Cell.add, Cell.scale, slotZero] at shiftStrict ⊢ <;>
    omega

/-- Splitting a forward tangent at its shifted gate does not change its
ordered unit subdivision. -/
theorem retainedTerminalFanCardinalForwardTangentRoute_unitSubdivide_eq_split
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance) :
    AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalForwardTangentRoute
          center port length slot distance) =
      AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalForwardTangentSplitRoute
          center port length slot distance) := by
  let route := retainedTerminalFanCardinalForwardTangentRoute
    center port length slot distance
  let splitRoute := retainedTerminalFanCardinalForwardTangentSplitRoute
    center port length slot distance
  have distancePositive : 0 < distance := by
    have spacingNonnegative :
        0 ≤ retainedTerminalFanOuterLaneSpacing * slot.val :=
      Nat.zero_le _
    omega
  have routeNonempty : route ≠ [] := by
    simp [route, retainedTerminalFanCardinalForwardTangentRoute]
  have splitRouteNonempty : splitRoute ≠ [] := by
    simp [splitRoute,
      retainedTerminalFanCardinalForwardTangentSplitRoute,
      retainedTerminalFanCardinalForwardTangentLeadingRoute,
      joinAtEndpoint]
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanCardinalForwardTangentRoute_orthogonal
      center port length slot distance cardinal distancePositive
  have splitRouteOrthogonal : OrthogonalPolyline splitRoute :=
    retainedTerminalFanCardinalForwardTangentSplitRoute_orthogonal
      center port length slot distance cardinal shiftStrict
  apply AxisDirection.unitSubdividePolyline_eq_of_head?_eq_of_directions_eq
    routeNonempty splitRouteNonempty routeOrthogonal splitRouteOrthogonal
  · simp [route, splitRoute,
      retainedTerminalFanCardinalForwardTangentRoute,
      retainedTerminalFanCardinalForwardTangentSplitRoute,
      retainedTerminalFanCardinalForwardTangentLeadingRoute,
      joinAtEndpoint]
  · rcases center with ⟨centerX, centerY⟩
    by_cases slotZero : slot.val = 0 <;>
      rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [route, splitRoute,
        retainedTerminalFanCardinalForwardTangentRoute,
        retainedTerminalFanCardinalForwardTangentSplitRoute,
        retainedTerminalFanCardinalForwardTangentLeadingRoute,
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
        translatePolyline, joinAtEndpoint,
        Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength, AxisDirection.between,
        Cell.add, Cell.scale, slotZero] at shiftStrict ⊢
    all_goals
      have slotPositive : 0 < slot.val :=
        Nat.pos_of_ne_zero slotZero
      have negativeCount :
          (8 * (slot.val : Int) - (distance : Int)).natAbs =
            distance - 8 * slot.val := by
        rw [show
          8 * (slot.val : Int) - (distance : Int) =
            -((distance - 8 * slot.val : Nat) : Int) by
          omega]
        simp
      have positiveCount :
          (-(8 * (slot.val : Int)) + (distance : Int)).natAbs =
            distance - 8 * slot.val := by
        rw [show
          -(8 * (slot.val : Int)) + (distance : Int) =
            ((distance - 8 * slot.val : Nat) : Int) by
          omega]
        simp
      have laneCount :
          (8 * (slot.val : Int)).natAbs = 8 * slot.val := by
        rw [Int.natAbs_mul]
        norm_num
      split_ifs <;> try omega
      simp only [negativeCount, positiveCount, laneCount]
      rw [← List.replicate_add]
      congr 1
      omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
