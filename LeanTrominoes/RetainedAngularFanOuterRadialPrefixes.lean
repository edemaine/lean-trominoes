/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialFinalStubs

/-!
# Strictly exterior prefixes of outer radial fan routes

Remove the last primitive block from an arbitrary-length radial raster.  The
remaining route ends one primitive outside its radius-288 lane port.  A
direction-dependent supporting side of the square proves that every point of
this prefix is strictly outside the complete finite local fan adapter.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Outward axis normal of the square side containing a direction's refined
lane ports. -/
def retainedTerminalFanOuterSideNormal :
    RetainedTerminalDirection → Cell
  | .compass OccurrenceSplitRing.Port.east => (1, 0)
  | .routedClause PlanarThreeSAT.DuplicatorArm.left => (1, 0)
  | .compass OccurrenceSplitRing.Port.southeast => (0, 1)
  | .compass OccurrenceSplitRing.Port.south => (0, 1)
  | .routedClause PlanarThreeSAT.DuplicatorArm.right => (0, 1)
  | .compass OccurrenceSplitRing.Port.southwest => (-1, 0)
  | .compass OccurrenceSplitRing.Port.west => (-1, 0)
  | .compass OccurrenceSplitRing.Port.northwest => (0, -1)
  | .compass OccurrenceSplitRing.Port.north => (0, -1)
  | .compass OccurrenceSplitRing.Port.northeast => (1, 0)
  | .routedClause PlanarThreeSAT.DuplicatorArm.middle => (1, 0)

/-- The selected side normal evaluates every exact lane port to radius
`288`. -/
theorem retainedTerminalFanOuterSideNormal_lanePortOffset :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal direction)
          (retainedTerminalFanOuterLanePortOffset direction slot) =
        288 := by
  native_decide

/-- Every retained primitive advances strictly outward through its selected
supporting side. -/
theorem retainedTerminalFanOuterSideNormal_primitive_positive :
    ∀ direction : RetainedTerminalDirection,
      0 <
        Cell.linearValue
          (retainedTerminalFanOuterSideNormal direction)
          direction.primitive := by
  native_decide

/-- The inward raster with its last primitive block removed. -/
def retainedTerminalFanOuterInwardPrefixRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  match terminal.1 with
  | .compass port =>
      .compass (oppositePort port)
        (retainedTerminalFanOuterRadialLength terminal - 1)
  | .routedClause arm =>
      .routedClause arm
        (retainedTerminalFanOuterRadialLength terminal - 1)

/-- Source-gate-to-one-block-outside prefix of an outer radial route. -/
def retainedTerminalFanOuterRadialPrefix
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate :=
    Cell.add gate
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  joinAtEndpoint
    (retainedTerminalFanOuterLaneShiftRouteAt
      gate terminal.1 slot)
    ((retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
      shiftedGate)

/-- Every radial prefix begins at the exact scaled source gate. -/
@[simp]
theorem retainedTerminalFanOuterRadialPrefix_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterRadialPrefix
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  apply joinAtEndpoint_head?
  exact retainedTerminalFanOuterLaneShiftRouteAt_head?
    _ terminal.1 slot

set_option maxRecDepth 4096 in
/-- Exact endpoint calculation for the shortened inward raster. -/
theorem retainedTerminalFanOuterInwardPrefix_finish_eq
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    Cell.add
        (Cell.add
          (retainedAngularFanOuterDemand
            center terminal slot).gate
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        (retainedTerminalFanOuterInwardPrefixRay terminal).vector =
      Cell.add center
        (Cell.add
          (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
          terminal.1.primitive) := by
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  rcases center with ⟨centerX, centerY⟩
  rcases terminal with ⟨direction, length⟩
  rcases direction with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    apply Prod.ext <;>
    simp [
      retainedTerminalFanOuterInwardPrefixRay,
      retainedTerminalFanOuterRadialLength,
      retainedTerminalFanOuterLanePortOffset,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanOuterLaneSpacing,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      RetainedTerminalDirection.primitive,
      RetainedRay.vector,
      oppositePort,
      OccurrenceSplitRing.Port.unitVector,
      routedClauseRayPrimitive,
      Cell.add, Cell.sub, Cell.scale]
      at radialLengthPositive ⊢ <;>
    omega

set_option maxRecDepth 4096 in
/-- A nonempty radial prefix ends exactly one outward primitive beyond its
positioned lane port. -/
@[simp]
theorem retainedTerminalFanOuterRadialPrefix_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterRadialPrefix
      center terminal slot).getLast? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
              terminal.1.primitive)) := by
  apply joinAtEndpoint_getLast?
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      _ terminal.1 slot)
    (RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardPrefixRay terminal) _)
  rw [RetainedRay.rasterize_getLast?]
  exact congrArg some
    (retainedTerminalFanOuterInwardPrefix_finish_eq
      center terminal slot radialLengthPositive)

/-- Removing the final primitive block preserves prefix orthogonality. -/
theorem retainedTerminalFanOuterRadialPrefix_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterRadialPrefix
        center terminal slot) := by
  apply
    (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      _ terminal.1 slot).joinAtEndpoint
      ((retainedTerminalFanOuterInwardPrefixRay
        terminal).rasterize_orthogonal _)
  · exact retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      _ terminal.1 slot
  · exact RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardPrefixRay terminal) _

@[simp]
theorem Cell.linearValue_scale
    (normal : Cell) (coefficient : Int) (point : Cell) :
    Cell.linearValue normal (Cell.scale coefficient point) =
      coefficient * Cell.linearValue normal point := by
  rcases normal with ⟨normalX, normalY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.linearValue, Cell.scale]
  ring

/-- If a diagonal block moves weakly inward in a linear functional and its
elbow does not overshoot the block endpoint, every staircase point lies at
least as far outward as the final endpoint. -/
theorem diagonalStaircase_linear_ge_finish
    (normal : Cell) (horizontal vertical : Int)
    (stepNonpositive :
      Cell.linearValue normal (horizontal, vertical) ≤ 0)
    (stepLeElbow :
      Cell.linearValue normal (horizontal, vertical) ≤
        Cell.linearValue normal (horizontal, 0))
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈
        diagonalStaircase horizontal vertical length start) :
    Cell.linearValue normal
        (Cell.add start
          (Cell.scale length (horizontal, vertical))) ≤
      Cell.linearValue normal point := by
  induction length generalizing start point with
  | zero =>
      simp [diagonalStaircase] at pointMember
      subst point
      simp
  | succ length induction =>
      simp only [diagonalStaircase,
        List.mem_cons] at pointMember
      rcases pointMember with rfl | rfl | trailingMember
      · rw [Cell.linearValue_add, Cell.linearValue_scale]
        have repeatedNonpositive :
            (length : Int) *
                Cell.linearValue normal
                  (horizontal, vertical) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (Int.natCast_nonneg length) stepNonpositive
        push_cast
        nlinarith
      · rw [Cell.linearValue_add, Cell.linearValue_scale,
          Cell.linearValue_add]
        have repeatedNonpositive :
            (length : Int) *
                Cell.linearValue normal
                  (horizontal, vertical) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (Int.natCast_nonneg length) stepNonpositive
        push_cast
        nlinarith
      · have trailing :=
          induction
            (Cell.add start (horizontal, vertical))
            point trailingMember
        simp only [Cell.linearValue_add,
          Cell.linearValue_scale] at trailing ⊢
        push_cast at trailing ⊢
        ring_nf at trailing ⊢
        exact trailing

/-- Every compass raster moves monotonically inward through its selected
supporting side. -/
theorem compassInwardRay_side_ge_finish
    (port : OccurrenceSplitRing.Port)
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈ compassRay (oppositePort port) length start) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (Cell.add start
          (Cell.scale length
            (oppositePort port).unitVector)) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        point := by
  cases port with
  | northwest =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          exact diagonalStaircase_linear_ge_finish
            _ 1 1 (by native_decide) (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
  | north =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          simp [compassRay, oppositePort] at pointMember
          rcases pointMember with rfl | rfl <;>
            simp [retainedTerminalFanOuterSideNormal,
              oppositePort,
              OccurrenceSplitRing.Port.unitVector,
              Cell.linearValue, Cell.add, Cell.scale]
  | northeast =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          exact diagonalStaircase_linear_ge_finish
            _ (-1) 1 (by native_decide) (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
  | east =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          simp [compassRay, oppositePort] at pointMember
          rcases pointMember with rfl | rfl <;>
            simp [retainedTerminalFanOuterSideNormal,
              oppositePort,
              OccurrenceSplitRing.Port.unitVector,
              Cell.linearValue, Cell.add, Cell.scale]
  | southeast =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          exact diagonalStaircase_linear_ge_finish
            _ (-1) (-1) (by native_decide) (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
  | south =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          simp [compassRay, oppositePort] at pointMember
          rcases pointMember with rfl | rfl <;>
            simp [retainedTerminalFanOuterSideNormal,
              oppositePort,
              OccurrenceSplitRing.Port.unitVector,
              Cell.linearValue, Cell.add, Cell.scale]
  | southwest =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          exact diagonalStaircase_linear_ge_finish
            _ 1 (-1) (by native_decide) (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
  | west =>
      cases length with
      | zero =>
          simp [compassRay] at pointMember
          subst point
          simp
      | succ length =>
          simp [compassRay, oppositePort] at pointMember
          rcases pointMember with rfl | rfl <;>
            simp [retainedTerminalFanOuterSideNormal,
              oppositePort,
              OccurrenceSplitRing.Port.unitVector,
              Cell.linearValue, Cell.add, Cell.scale]

/-- Every point of an exceptional primitive block lies outward of its
endpoint in the selected supporting side. -/
theorem routedClauseRayOffsets_side_ge_primitive :
    ∀ (arm : PlanarThreeSAT.DuplicatorArm)
      (offset : Cell),
      offset ∈ routedClauseRayOffsets arm →
        Cell.linearValue
            (retainedTerminalFanOuterSideNormal (.routedClause arm))
            (routedClauseRayPrimitive arm) ≤
          Cell.linearValue
            (retainedTerminalFanOuterSideNormal (.routedClause arm))
            offset := by
  native_decide

/-- Each exceptional inward primitive moves strictly toward the selected
supporting side's interior. -/
theorem routedClauseRayPrimitive_side_negative :
    ∀ arm : PlanarThreeSAT.DuplicatorArm,
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal (.routedClause arm))
          (routedClauseRayPrimitive arm) < 0 := by
  native_decide

/-- A translated exceptional primitive block stays outward of its
endpoint. -/
theorem routedClauseRayBlock_side_ge_finish
    (arm : PlanarThreeSAT.DuplicatorArm)
    (start point : Cell)
    (pointMember : point ∈ routedClauseRayBlock arm start) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.routedClause arm))
        (Cell.add start (routedClauseRayPrimitive arm)) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.routedClause arm))
        point := by
  rw [routedClauseRayBlock, List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  rw [Cell.linearValue_add, Cell.linearValue_add]
  simpa [add_comm] using
    (add_le_add_left
      (routedClauseRayOffsets_side_ge_primitive
        arm offset offsetMember)
      (Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.routedClause arm))
        start))

/-- Every repeated exceptional raster moves monotonically inward through
its selected supporting side. -/
theorem routedClauseRay_side_ge_finish
    (arm : PlanarThreeSAT.DuplicatorArm)
    (length : Nat) (start point : Cell)
    (pointMember : point ∈ routedClauseRay arm length start) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.routedClause arm))
        (Cell.add start
          (Cell.scale length (routedClauseRayPrimitive arm))) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.routedClause arm))
        point := by
  induction length generalizing start point with
  | zero =>
      simp [routedClauseRay] at pointMember
      subst point
      simp
  | succ length induction =>
      rw [routedClauseRay] at pointMember
      rcases mem_joinAtEndpoint pointMember with
          blockMember | trailingMember
      · have block :=
          routedClauseRayBlock_side_ge_finish
            arm start point blockMember
        have primitiveNegative :=
          routedClauseRayPrimitive_side_negative arm
        rw [Cell.linearValue_add, Cell.linearValue_scale]
        have repeatedNonpositive :
            (length : Int) *
                Cell.linearValue
                  (retainedTerminalFanOuterSideNormal
                    (.routedClause arm))
                  (routedClauseRayPrimitive arm) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (Int.natCast_nonneg length)
            (le_of_lt primitiveNegative)
        push_cast
        rw [Cell.linearValue_add] at block
        nlinarith
      · have trailing :=
          induction
            (Cell.add start (routedClauseRayPrimitive arm))
            point trailingMember
        simp only [Cell.linearValue_add,
          Cell.linearValue_scale] at trailing ⊢
        push_cast at trailing ⊢
        ring_nf at trailing ⊢
        exact trailing

/-- The shortened inward raster stays outward of its exact final point in
the supporting-side functional. -/
theorem retainedTerminalFanOuterInwardPrefixRay_side_ge_finish
    (direction : RetainedTerminalDirection)
    (terminalLength : Nat)
    (start point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterInwardPrefixRay
          (direction, terminalLength)).rasterize start) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        (Cell.add start
          (retainedTerminalFanOuterInwardPrefixRay
            (direction, terminalLength)).vector) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        point := by
  cases direction with
  | compass port =>
      exact compassInwardRay_side_ge_finish
        port
        (retainedTerminalFanOuterRadialLength
          (.compass port, terminalLength) - 1)
        start point
        (by simpa [retainedTerminalFanOuterInwardPrefixRay,
          RetainedRay.rasterize, RetainedRay.vector]
          using pointMember)
  | routedClause arm =>
      exact routedClauseRay_side_ge_finish
        arm
        (retainedTerminalFanOuterRadialLength
          (.routedClause arm, terminalLength) - 1)
        start point
        (by simpa [retainedTerminalFanOuterInwardPrefixRay,
          RetainedRay.rasterize, RetainedRay.vector]
          using pointMember)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Every point of a nonempty radial prefix lies strictly outside the
supporting side of the radius-288 square. -/
theorem retainedTerminalFanOuterRadialPrefix_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialPrefix
        center terminal slot) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  let gate :=
    (retainedAngularFanOuterDemand
      center terminal slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor terminal)
            (retainedTerminalFanRefinedInterfaceOffset terminal.1)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center terminal slot
  rw [retainedTerminalFanOuterRadialPrefix] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate terminal.1 slot)
      ((retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
        (Cell.add gate
          (retainedTerminalFanOuterLaneOffset
            terminal.1 slot))) at pointMember
  rcases mem_joinAtEndpoint pointMember with
      shiftMember | rasterMember
  · unfold retainedTerminalFanOuterLaneShiftRouteAt
      PeriodicOrthocrossing.translatePolyline at shiftMember
    rw [List.mem_map] at shiftMember
    rcases shiftMember with ⟨offset, offsetMember, rfl⟩
    by_cases slotZero : slot.val = 0
    · simp [retainedTerminalFanOuterLaneShiftRoute,
        slotZero] at offsetMember
      subst offset
      rw [gateEq]
      rcases terminal with ⟨direction, length⟩
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSideNormal,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
          at radialLengthPositive ⊢ <;>
        omega
    · simp [retainedTerminalFanOuterLaneShiftRoute,
        slotZero] at offsetMember
      rcases offsetMember with rfl | rfl
      · rw [gateEq]
        rcases terminal with ⟨direction, length⟩
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          simp [
            retainedTerminalFanOuterSideNormal,
            retainedTerminalFanOuterRadialLength,
            retainedTerminalFanTotalRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            RetainedTerminalDirection.primitive,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at radialLengthPositive ⊢ <;>
          omega
      · rw [gateEq]
        rcases terminal with ⟨direction, length⟩
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          simp [
            retainedTerminalFanOuterSideNormal,
            retainedTerminalFanOuterRadialLength,
            retainedTerminalFanTotalRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            RetainedTerminalDirection.primitive,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
            at radialLengthPositive ⊢ <;>
          omega
  · have outward :=
      retainedTerminalFanOuterInwardPrefixRay_side_ge_finish
        terminal.1 terminal.2
        (Cell.add gate
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        point rasterMember
    have finishEq :=
      retainedTerminalFanOuterInwardPrefix_finish_eq
        center terminal slot radialLengthPositive
    rw [finishEq] at outward
    rw [Cell.linearValue_add, Cell.linearValue_add,
      retainedTerminalFanOuterSideNormal_lanePortOffset]
      at outward
    have primitivePositive :=
      retainedTerminalFanOuterSideNormal_primitive_positive terminal.1
    omega

/-- Every positioned local fan route lies on the weak inner side of every
retained direction's radius-288 supporting line. -/
theorem retainedTerminalFanOuterLocalRouteAt_side_upper
    (center : Cell)
    (sideDirection localDirection : RetainedTerminalDirection)
    (localSlot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLocalRouteAt
        center localDirection localSlot) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal sideDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal sideDirection)
          center +
        288 := by
  unfold retainedTerminalFanOuterLocalRouteAt at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  have bounded :=
    retainedTerminalFanOuterLocalRoute_points_within_outer_frame
      localDirection localSlot offset offsetMember
  have coordinateBounds := bounded.coordinate_bounds
  rcases sideDirection with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterSideNormal,
      Cell.linearValue, Cell.add] at coordinateBounds ⊢ <;>
    omega

/-- A nonempty radial prefix is continuously separated from every complete
positioned local fan route, independently of angular order. -/
theorem retainedTerminalFanOuterRadialPrefix_strictlyAvoid_local
    (center : Cell)
    (terminal : RetainedTerminalData)
    (radialSlot localSlot : RetainedTerminalSlot)
    (localDirection : RetainedTerminalDirection)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialPrefix
        center terminal radialSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center localDirection localSlot) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 288)
      (retainedTerminalFanOuterLocalRouteAt_side_upper
        center terminal.1 localDirection localSlot)
      (retainedTerminalFanOuterRadialPrefix_side_lower
        center terminal radialSlot radialLengthPositive)).symm

/-- Symmetric orientation of exterior-prefix versus local-route
separation. -/
theorem retainedTerminalFanOuterLocal_strictlyAvoid_radialPrefix
    (center : Cell)
    (localDirection : RetainedTerminalDirection)
    (localSlot radialSlot : RetainedTerminalSlot)
    (terminal : RetainedTerminalData)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center localDirection localSlot)
      (retainedTerminalFanOuterRadialPrefix
        center terminal radialSlot) := by
  exact
    (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_local
      center terminal radialSlot localSlot localDirection
      radialLengthPositive).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
