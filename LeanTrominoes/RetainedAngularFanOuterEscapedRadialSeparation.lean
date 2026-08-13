/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedSourceSeparation
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation

/-!
# Separation of escaped radial routes in different directions

An escaped radial route has three pieces: an unshifted source ray, a delayed
lane shift, and a shifted remaining ray.  Retaining this exact decomposition
lets the ordinary angular separator table see the lane offset near the fan
interface, where a single coarse corridor would lose the strict gap.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem sourceEscapeRay_length
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterSourceEscapeRay terminal).length =
      retainedTerminalFanOuterSourceEscapeLength := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem sourceEscapeRay_primitive
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterSourceEscapeRay terminal).primitive =
      (retainedTerminalFanOuterInwardRay terminal).primitive := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem sourceEscapePoint_eq_checkpoint
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterSourceEscapePoint center terminal slot =
      Cell.add
        (retainedAngularFanOuterDemand center terminal slot).gate
        (Cell.scale retainedTerminalFanOuterSourceEscapeLength
          (retainedTerminalFanOuterInwardRay terminal).primitive) := by
  unfold retainedTerminalFanOuterSourceEscapePoint
  rw [RetainedRay.vector_eq_scale_length_primitive,
    sourceEscapeRay_length, sourceEscapeRay_primitive]

/-- An escaped radial point belongs to one of its three exact pieces: the
source raster, the delayed lane shift, or the shifted remaining raster. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_point_in_exact_piece
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedRadialRoute
          center terminal slot) :
    let gate :=
      (retainedAngularFanOuterDemand center terminal slot).gate
    let primitive :=
      (retainedTerminalFanOuterInwardRay terminal).primitive
    point ∈
        (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate ∨
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (Cell.add gate
            (Cell.scale retainedTerminalFanOuterSourceEscapeLength
              primitive))
          terminal.1 slot ∨
      point ∈
        (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          (Cell.add
            (Cell.add gate
              (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                primitive))
            (retainedTerminalFanOuterLaneOffset terminal.1 slot)) := by
  dsimp only
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  rw [retainedTerminalFanOuterEscapedRadialRoute] at pointMember
  change
    point ∈
      joinAtEndpoint
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate)
        (joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            escapePoint terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
            shiftedEscapePoint)) at pointMember
  rcases mem_joinAtEndpoint pointMember with
      sourceMember | shiftedTailMember
  · left
    exact sourceMember
  · rcases mem_joinAtEndpoint shiftedTailMember with
      shiftMember | remainingMember
    · right
      left
      simpa [escapePoint, sourceEscapePoint_eq_checkpoint]
        using shiftMember
    · right
      right
      simpa [shiftedEscapePoint, escapePoint,
        sourceEscapePoint_eq_checkpoint, Cell.add, Cell.scale]
        using remainingMember

/-- The delayed lane shift of an earlier-direction escaped route remains on
the weak side of the ordinary angular separator. -/
theorem retainedTerminalFanOuterDelayedLaneShift_linear_upper
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotLtSeven : slot.val < 7)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (firstDirection, length))
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (Cell.add
            (retainedAngularFanOuterDemand
              center (firstDirection, length) slot).gate
            (Cell.scale retainedTerminalFanOuterSourceEscapeLength
              (retainedTerminalFanOuterInwardRay
                (firstDirection, length)).primitive))
          firstDirection slot) :
    Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection secondDirection)
          center +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection secondDirection := by
  have gateEq :=
    retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (firstDirection, length) slot
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline
    retainedTerminalFanOuterLaneShiftRoute at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with
    ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · simp [slotZero] at offsetMember
    subst offset
    rw [gateEq]
    rcases firstDirection with
      _ | _ <;>
      rename_i firstKind <;>
      cases firstKind <;>
      rcases secondDirection with
        _ | _ <;>
        rename_i secondKind <;>
        cases secondKind <;>
        simp [
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          RetainedRay.primitive,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalFanOuterRadialSeparatorNormal,
          retainedTerminalFanOuterRadialSeparatorBound,
          RetainedTerminalDirection.angularRank,
          RetainedTerminalDirection.primitive,
          oppositePort,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at directionsLt lengthPositive escapeFits ⊢ <;>
        omega
  · simp [slotZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · rw [gateEq]
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.primitive,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt lengthPositive escapeFits ⊢ <;>
          omega
    · rw [gateEq]
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.primitive,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt lengthPositive slotLtSeven escapeFits ⊢ <;>
          omega

/-- The delayed lane shift of a later-direction escaped route remains
strictly beyond the ordinary angular separator. -/
theorem retainedTerminalFanOuterDelayedLaneShift_linear_lower
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotPositive : 0 < slot.val)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (secondDirection, length))
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (Cell.add
            (retainedAngularFanOuterDemand
              center (secondDirection, length) slot).gate
            (Cell.scale retainedTerminalFanOuterSourceEscapeLength
              (retainedTerminalFanOuterInwardRay
                (secondDirection, length)).primitive))
          secondDirection slot) :
    Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection secondDirection)
          center +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection secondDirection <
      Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        point := by
  have gateEq :=
    retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (secondDirection, length) slot
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline
    retainedTerminalFanOuterLaneShiftRoute at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with
    ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · omega
  · simp [slotZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · rw [gateEq]
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.primitive,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt lengthPositive escapeFits ⊢ <;>
          omega
    · rw [gateEq]
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.primitive,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt lengthPositive slotPositive escapeFits ⊢ <;>
          omega

/-- Every escaped radial point in the earlier direction stays on the weak
side of the ordinary angular separator. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_linear_upper
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotLtSeven : slot.val < 7)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (firstDirection, length))
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedRadialRoute
          center (firstDirection, length) slot) :
    Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection secondDirection)
          center +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection secondDirection := by
  let terminal : RetainedTerminalData := (firstDirection, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor terminal)
            (retainedTerminalFanRefinedInterfaceOffset
              firstDirection)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center terminal slot
  have pieces :=
    retainedTerminalFanOuterEscapedRadialRoute_point_in_exact_piece
      center terminal slot pointMember
  change
    point ∈
        (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate ∨
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (Cell.add gate
            (Cell.scale retainedTerminalFanOuterSourceEscapeLength
              (retainedTerminalFanOuterInwardRay terminal).primitive))
          firstDirection slot ∨
      point ∈
        (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          (Cell.add
            (Cell.add gate
              (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                (retainedTerminalFanOuterInwardRay terminal).primitive))
            (retainedTerminalFanOuterLaneOffset firstDirection slot))
      at pieces
  rcases pieces with
      sourceMember | shiftMember | remainingMember
  · by_cases wrapPair :
        firstDirection =
            .compass OccurrenceSplitRing.Port.east ∧
          secondDirection =
            .routedClause PlanarThreeSAT.DuplicatorArm.middle
    · rcases wrapPair with ⟨rfl, rfl⟩
      have sameY :=
        compassRay_west_snd
          retainedTerminalFanOuterSourceEscapeLength
          gate point
          (by
            simpa [terminal,
              retainedTerminalFanOuterSourceEscapeRay,
              retainedTerminalFanOuterInwardRayOfLength,
              RetainedRay.rasterize, oppositePort] using
                sourceMember)
      rw [gateEq] at sameY
      simp [
        terminal,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalFanOuterRadialSeparatorNormal,
        retainedTerminalFanOuterRadialSeparatorBound,
        RetainedTerminalDirection.angularRank,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        Cell.linearValue, Cell.add, Cell.scale]
        at sameY ⊢
      omega
    · rcases
        (retainedTerminalFanOuterSourceEscapeRay terminal)
          |>.rasterize_point_near_checkpoint
            gate sourceMember with
        ⟨index, indexLe, nearby⟩
      rw [gateEq] at nearby
      have coordinateBounds := nearby.coordinate_bounds
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            terminal,
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterSourceEscapeRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.length, RetainedRay.primitive,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at indexLe coordinateBounds directionsLt
              lengthPositive wrapPair escapeFits ⊢ <;>
          omega
  · exact
      retainedTerminalFanOuterDelayedLaneShift_linear_upper
        center firstDirection secondDirection length slot
        directionsLt lengthPositive slotLtSeven escapeFits
        point
        (by simpa [terminal, gate] using shiftMember)
  · by_cases wrapPair :
        firstDirection =
            .compass OccurrenceSplitRing.Port.east ∧
          secondDirection =
            .routedClause PlanarThreeSAT.DuplicatorArm.middle
    · rcases wrapPair with ⟨rfl, rfl⟩
      have sameY :=
        compassRay_west_snd
          (retainedTerminalFanOuterRadialLength
              (.compass OccurrenceSplitRing.Port.east, length) -
            retainedTerminalFanOuterSourceEscapeLength)
          (Cell.add
            (Cell.add gate
              (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                (retainedTerminalFanOuterInwardRay terminal).primitive))
            (retainedTerminalFanOuterLaneOffset
              (.compass OccurrenceSplitRing.Port.east) slot))
          point
          (by
            simpa [terminal,
              retainedTerminalFanOuterEscapedRemainingRay,
              retainedTerminalFanOuterInwardRayOfLength,
              RetainedRay.rasterize, oppositePort] using
                remainingMember)
      rw [gateEq] at sameY
      simp [
        terminal,
        retainedTerminalFanOuterSourceEscapeLength,
        retainedTerminalFanOuterInwardRay,
        RetainedRay.primitive,
        retainedTerminalFanOuterLaneOffset,
        retainedTerminalFanOuterLaneStep,
        retainedTerminalFanOuterLaneSpacing,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalFanOuterRadialSeparatorNormal,
        retainedTerminalFanOuterRadialSeparatorBound,
        RetainedTerminalDirection.angularRank,
        RetainedTerminalDirection.primitive,
        oppositePort,
        OccurrenceSplitRing.Port.unitVector,
        Cell.linearValue, Cell.add, Cell.scale]
        at sameY ⊢
      omega
    · rcases
        (retainedTerminalFanOuterEscapedRemainingRay terminal)
          |>.rasterize_point_near_checkpoint
            (Cell.add
              (Cell.add gate
                (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                  (retainedTerminalFanOuterInwardRay terminal).primitive))
              (retainedTerminalFanOuterLaneOffset firstDirection slot))
            remainingMember with
        ⟨index, indexLe, nearby⟩
      rw [gateEq] at nearby
      have coordinateBounds := nearby.coordinate_bounds
      rcases firstDirection with
        _ | _ <;>
        rename_i firstKind <;>
        cases firstKind <;>
        rcases secondDirection with
          _ | _ <;>
          rename_i secondKind <;>
          cases secondKind <;>
          simp [
            terminal,
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanOuterEscapedRemainingRay,
            retainedTerminalFanOuterInwardRayOfLength,
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterRadialLength,
            RetainedRay.length, RetainedRay.primitive,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterRadialSeparatorNormal,
            retainedTerminalFanOuterRadialSeparatorBound,
            RetainedTerminalDirection.angularRank,
            RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at indexLe coordinateBounds directionsLt lengthPositive
              slotLtSeven wrapPair escapeFits ⊢ <;>
          omega

/-- Every escaped radial point in the later direction stays strictly on the
far side of the ordinary angular separator. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_linear_lower
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotPositive : 0 < slot.val)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (secondDirection, length))
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedRadialRoute
          center (secondDirection, length) slot) :
    Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection secondDirection)
          center +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection secondDirection <
      Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        point := by
  let terminal : RetainedTerminalData := (secondDirection, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor terminal)
            (retainedTerminalFanRefinedInterfaceOffset
              secondDirection)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center terminal slot
  have pieces :=
    retainedTerminalFanOuterEscapedRadialRoute_point_in_exact_piece
      center terminal slot pointMember
  change
    point ∈
        (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate ∨
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (Cell.add gate
            (Cell.scale retainedTerminalFanOuterSourceEscapeLength
              (retainedTerminalFanOuterInwardRay terminal).primitive))
          secondDirection slot ∨
      point ∈
        (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          (Cell.add
            (Cell.add gate
              (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                (retainedTerminalFanOuterInwardRay terminal).primitive))
            (retainedTerminalFanOuterLaneOffset secondDirection slot))
      at pieces
  rcases pieces with
      sourceMember | shiftMember | remainingMember
  · rcases
      (retainedTerminalFanOuterSourceEscapeRay terminal)
        |>.rasterize_point_near_checkpoint
          gate sourceMember with
      ⟨index, indexLe, nearby⟩
    rw [gateEq] at nearby
    have coordinateBounds := nearby.coordinate_bounds
    rcases firstDirection with
      _ | _ <;>
      rename_i firstKind <;>
      cases firstKind <;>
      rcases secondDirection with
        _ | _ <;>
        rename_i secondKind <;>
        cases secondKind <;>
        simp [
          terminal,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterInwardRayOfLength,
          RetainedRay.length, RetainedRay.primitive,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalFanOuterRadialSeparatorNormal,
          retainedTerminalFanOuterRadialSeparatorBound,
          RetainedTerminalDirection.angularRank,
          RetainedTerminalDirection.primitive,
          oppositePort,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at indexLe coordinateBounds directionsLt
            lengthPositive escapeFits ⊢ <;>
        omega
  · exact
      retainedTerminalFanOuterDelayedLaneShift_linear_lower
        center firstDirection secondDirection length slot
        directionsLt lengthPositive slotPositive escapeFits
        point
        (by simpa [terminal, gate] using shiftMember)
  · rcases
      (retainedTerminalFanOuterEscapedRemainingRay terminal)
        |>.rasterize_point_near_checkpoint
          (Cell.add
            (Cell.add gate
              (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                (retainedTerminalFanOuterInwardRay terminal).primitive))
            (retainedTerminalFanOuterLaneOffset secondDirection slot))
          remainingMember with
      ⟨index, indexLe, nearby⟩
    rw [gateEq] at nearby
    have coordinateBounds := nearby.coordinate_bounds
    rcases firstDirection with
      _ | _ <;>
      rename_i firstKind <;>
      cases firstKind <;>
      rcases secondDirection with
        _ | _ <;>
        rename_i secondKind <;>
        cases secondKind <;>
        simp [
          terminal,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterEscapedRemainingRay,
          retainedTerminalFanOuterInwardRayOfLength,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          RetainedRay.length, RetainedRay.primitive,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalFanOuterRadialSeparatorNormal,
          retainedTerminalFanOuterRadialSeparatorBound,
          RetainedTerminalDirection.angularRank,
          RetainedTerminalDirection.primitive,
          oppositePort,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at indexLe coordinateBounds directionsLt lengthPositive
            slotPositive escapeFits ⊢ <;>
        omega

/-- Escaped radial routes in strictly ordered directions and occurrence
slots are strictly separated for arbitrary positive terminal lengths. -/
theorem retainedTerminalFanOuterEscapedRadialRoutes_strictlyAvoid_of_direction_lt
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (slotsLt : firstSlot.val < secondSlot.val)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (firstDirection, firstLength))
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (secondDirection, secondLength)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterEscapedRadialRoute
        center (secondDirection, secondLength) secondSlot) := by
  have firstSlotLtSeven : firstSlot.val < 7 := by
    have secondSlotLt := secondSlot.isLt
    omega
  have secondSlotPositive : 0 < secondSlot.val := by
    omega
  exact routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterRadialSeparatorNormal
      firstDirection secondDirection)
    (Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection secondDirection)
        center +
      retainedTerminalFanOuterRadialSeparatorBound
        firstDirection secondDirection)
    (retainedTerminalFanOuterEscapedRadialRoute_linear_upper
      center firstDirection secondDirection firstLength firstSlot
      directionsLt firstLengthPositive firstSlotLtSeven firstEscapeFits)
    (retainedTerminalFanOuterEscapedRadialRoute_linear_lower
      center firstDirection secondDirection secondLength secondSlot
      directionsLt secondLengthPositive secondSlotPositive
      secondEscapeFits)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
