import LeanTrominoes.RetainedAngularFanOuterCompleteRoutes
import LeanTrominoes.OrthogonalPolylineLinearSeparation

/-!
# Separation of arbitrary-length outer radial fan routes

The finite fan adapter is already separated inside the radius-288 frame.
This file treats the unbounded source-gate-to-frame pieces.  Distinct
retained directions are separated by explicit integer half-planes.  The
finite table contains only a normal and threshold for each ordered pair of
the eleven direction ranks; arbitrary radial length is handled through the
uniform radius-nine retained-ray corridor bound.

Same-direction nested lanes require a parallel-track argument and are
developed after the angular half-plane case.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Coordinate inequalities extracted from a closed coordinate-radius
bound. -/
theorem WithinCoordinateRadius.coordinate_bounds
    {radius : Nat} {center point : Cell}
    (bounded : WithinCoordinateRadius radius center point) :
    ((center.1 - radius : Int) ≤ point.1 ∧
      point.1 ≤ center.1 + radius) ∧
    ((center.2 - radius : Int) ≤ point.2 ∧
      point.2 ≤ center.2 + radius) := by
  have natAbsBounds
      {delta : Int} {bound : Nat}
      (absolute : delta.natAbs ≤ bound) :
      -(bound : Int) ≤ delta ∧
        delta ≤ (bound : Int) := by
    by_cases nonnegative : 0 ≤ delta
    · have castAbsolute :
          (delta.natAbs : Int) ≤ (bound : Int) := by
        exact_mod_cast absolute
      rw [Int.natAbs_of_nonneg nonnegative] at castAbsolute
      omega
    · have nonpositive : delta ≤ 0 :=
        le_of_not_ge nonnegative
      have negativeNonnegative : 0 ≤ -delta := by
        omega
      have absoluteNegative :
          (-delta).natAbs ≤ bound := by
        simpa using absolute
      have castAbsolute :
          ((-delta).natAbs : Int) ≤ (bound : Int) := by
        exact_mod_cast absoluteNegative
      rw [Int.natAbs_of_nonneg negativeNonnegative]
        at castAbsolute
      omega
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases bounded with ⟨horizontal, vertical⟩
  have horizontalBounds := natAbsBounds horizontal
  have verticalBounds := natAbsBounds vertical
  omega

/-- Half-plane normal separating two distinct direction ranks.  Only the
strict-rank-order cases are used below. -/
def retainedTerminalFanOuterRadialSeparatorNormal
    (first second : RetainedTerminalDirection) : Cell :=
  match first.angularRank, second.angularRank with
  | 0, 1 => (0, 1)
  | 0, 2 | 1, 2 => (-1, 1)
  | 0, 3 | 0, 4 | 1, 3 | 1, 4 |
      2, 3 | 2, 4 | 3, 4 => (-1, 0)
  | 0, 5 | 0, 6 | 0, 7 | 0, 8 | 0, 9 |
      1, 5 | 1, 6 | 1, 7 | 1, 8 | 1, 9 |
      2, 5 | 2, 6 | 2, 7 | 2, 8 | 2, 9 |
      3, 5 | 3, 6 | 3, 7 | 3, 8 | 3, 9 |
      4, 5 | 4, 6 | 4, 7 | 4, 8 | 4, 9 |
      5, 6 | 5, 7 | 5, 8 => (-1, -1)
  | 0, 10 | 1, 10 | 2, 10 | 3, 10 | 4, 10 |
      5, 9 | 5, 10 | 6, 7 | 6, 8 | 6, 9 => (0, -1)
  | 6, 10 | 7, 8 | 7, 9 | 7, 10 => (1, -1)
  | 8, 9 | 8, 10 => (1, 0)
  | 9, 10 => (1, 1)
  | _, _ => (0, 0)

/-- Conservative centered threshold for the corresponding separating
half-plane.  The margins include the full radius-nine staircase corridor. -/
def retainedTerminalFanOuterRadialSeparatorBound
    (first second : RetainedTerminalDirection) : Int :=
  match first.angularRank, second.angularRank with
  | 0, 1 => 64
  | 0, 2 => -200
  | 0, 3 | 0, 4 => -270
  | 0, 5 | 0, 6 | 0, 7 | 0, 8 | 0, 9 => -250
  | 0, 10 => 0
  | 1, 2 => -80
  | 1, 3 | 1, 4 => -270
  | 1, 5 | 1, 6 | 1, 7 | 1, 8 | 1, 9 => -380
  | 1, 10 => -110
  | 2, 3 | 2, 4 => -220
  | 2, 5 | 2, 6 | 2, 7 | 2, 8 | 2, 9 => -500
  | 2, 10 => -270
  | 3, 4 => 60
  | 3, 5 | 3, 6 | 3, 7 | 3, 8 | 3, 9 => -210
  | 3, 10 => -270
  | 4, 5 | 4, 6 | 4, 7 | 4, 8 | 4, 9 => -140
  | 4, 10 => -270
  | 5, 6 | 5, 7 | 5, 8 => 80
  | 5, 9 | 5, 10 => -220
  | 6, 7 | 6, 8 | 6, 9 => 70
  | 6, 10 => -210
  | 7, 8 | 7, 9 | 7, 10 => 80
  | 8, 9 | 8, 10 => 70
  | 9, 10 => 80
  | _, _ => 0

/-- Every listed point of a direct west compass ray has the starting
vertical coordinate. -/
theorem compassRay_west_snd
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈
        compassRay OccurrenceSplitRing.Port.west
          length start) :
    point.2 = start.2 := by
  cases length with
  | zero =>
      simp [compassRay] at pointMember
      subst point
      rfl
  | succ length =>
      simp [compassRay] at pointMember
      rcases pointMember with rfl | rfl
      · rfl
      · simp [OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale]

set_option maxHeartbeats 2000000 in
/-- The short tangential entrance of an earlier-direction route lies on
the weak side of the same separating half-plane. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_linear_upper
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotLtSeven : slot.val < 7)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLaneShiftRouteAt
        (retainedAngularFanOuterDemand
          center (firstDirection, length) slot).gate
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
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
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
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at directionsLt ⊢ <;>
        omega
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
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
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt ⊢ <;>
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
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at directionsLt slotLtSeven ⊢ <;>
          omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every point of the earlier-direction radial route lies on the weak
side of its separating half-plane. -/
theorem retainedTerminalFanOuterRadialRoute_linear_upper
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotLtSeven : slot.val < 7)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialRoute
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
  let gate :=
    (retainedAngularFanOuterDemand
      center (firstDirection, length) slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor
              (firstDirection, length))
            (retainedTerminalFanRefinedInterfaceOffset
              firstDirection)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (firstDirection, length) slot
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate firstDirection slot)
      ((retainedTerminalFanOuterInwardRay
        (firstDirection, length)).rasterize
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              firstDirection slot))) at pointMember
  rcases mem_joinAtEndpoint pointMember with
      shiftMember | rasterMember
  · exact
      retainedTerminalFanOuterLaneShiftRouteAt_linear_upper
        center firstDirection secondDirection length slot
        directionsLt lengthPositive slotLtSeven point
        shiftMember
  · by_cases wrapPair :
      firstDirection =
          .compass OccurrenceSplitRing.Port.east ∧
        secondDirection =
          .routedClause PlanarThreeSAT.DuplicatorArm.middle
    · rcases wrapPair with ⟨rfl, rfl⟩
      have sameY :=
        compassRay_west_snd
          (retainedTerminalFanOuterRadialLength
            (.compass OccurrenceSplitRing.Port.east, length))
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              (.compass OccurrenceSplitRing.Port.east) slot))
          point
          (by
            simpa [retainedTerminalFanOuterInwardRay,
              RetainedRay.rasterize, oppositePort] using
                rasterMember)
      rw [gateEq] at sameY
      simp [
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
        OccurrenceSplitRing.Port.unitVector,
        Cell.linearValue, Cell.add, Cell.scale]
        at sameY ⊢
      omega
    · rcases
        (retainedTerminalFanOuterInwardRay
          (firstDirection, length)).rasterize_point_near_checkpoint
            (Cell.add gate
              (retainedTerminalFanOuterLaneOffset
                firstDirection slot))
            rasterMember with
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
            at indexLe coordinateBounds directionsLt
              slotLtSeven wrapPair ⊢ <;>
          omega

set_option maxHeartbeats 2000000 in
/-- The short tangential entrance of a later-direction route lies strictly
on the far side of the separating half-plane. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_linear_lower
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotPositive : 0 < slot.val)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLaneShiftRouteAt
        (retainedAngularFanOuterDemand
          center (secondDirection, length) slot).gate
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
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  have slotNonzero : slot.val ≠ 0 := by
    omega
  simp [retainedTerminalFanOuterLaneShiftRoute,
    slotNonzero] at offsetMember
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
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at directionsLt ⊢ <;>
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
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at directionsLt slotPositive ⊢ <;>
        omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every point of the later-direction radial route lies strictly on the
far side of its separating half-plane. -/
theorem retainedTerminalFanOuterRadialRoute_linear_lower
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (lengthPositive : 0 < length)
    (slotPositive : 0 < slot.val)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialRoute
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
  let gate :=
    (retainedAngularFanOuterDemand
      center (secondDirection, length) slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor
              (secondDirection, length))
            (retainedTerminalFanRefinedInterfaceOffset
              secondDirection)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (secondDirection, length) slot
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate secondDirection slot)
      ((retainedTerminalFanOuterInwardRay
        (secondDirection, length)).rasterize
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              secondDirection slot))) at pointMember
  rcases mem_joinAtEndpoint pointMember with
      shiftMember | rasterMember
  · exact
      retainedTerminalFanOuterLaneShiftRouteAt_linear_lower
        center firstDirection secondDirection length slot
        directionsLt lengthPositive slotPositive point
        shiftMember
  · rcases
      (retainedTerminalFanOuterInwardRay
        (secondDirection, length)).rasterize_point_near_checkpoint
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              secondDirection slot))
          rasterMember with
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
          at indexLe coordinateBounds directionsLt
            slotPositive ⊢ <;>
        omega

/-- Radial routes in two strictly ordered retained directions have complete
continuous separation, independently of their positive radial lengths. -/
theorem retainedTerminalFanOuterRadialRoutes_strictlyAvoid_of_direction_lt
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstDirection.angularRank <
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterRadialRoute
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
    (retainedTerminalFanOuterRadialRoute_linear_upper
      center firstDirection secondDirection firstLength firstSlot
      directionsLt firstLengthPositive firstSlotLtSeven)
    (retainedTerminalFanOuterRadialRoute_linear_lower
      center firstDirection secondDirection secondLength secondSlot
      directionsLt secondLengthPositive secondSlotPositive)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
