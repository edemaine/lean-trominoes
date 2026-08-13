/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- Linear functional perpendicular to one retained terminal primitive and
positive on its clockwise lane-step direction. -/
def retainedTerminalFanOuterTransverseNormal :
    RetainedTerminalDirection → Cell
  | .compass OccurrenceSplitRing.Port.east => (0, 1)
  | .routedClause PlanarThreeSAT.DuplicatorArm.left => (-4, 9)
  | .compass OccurrenceSplitRing.Port.southeast => (-1, 1)
  | .compass OccurrenceSplitRing.Port.south => (-1, 0)
  | .routedClause PlanarThreeSAT.DuplicatorArm.right => (-4, -1)
  | .compass OccurrenceSplitRing.Port.southwest => (-1, -1)
  | .compass OccurrenceSplitRing.Port.west => (0, -1)
  | .compass OccurrenceSplitRing.Port.northwest => (1, -1)
  | .compass OccurrenceSplitRing.Port.north => (1, 0)
  | .compass OccurrenceSplitRing.Port.northeast => (1, 1)
  | .routedClause PlanarThreeSAT.DuplicatorArm.middle => (1, 4)

/-- Minimum transverse deviation within one primitive inward staircase
block. -/
def retainedTerminalFanOuterTransverseLowerDeviation :
    RetainedTerminalDirection → Int
  | .routedClause PlanarThreeSAT.DuplicatorArm.left => -4
  | .routedClause PlanarThreeSAT.DuplicatorArm.right => -2
  | .routedClause PlanarThreeSAT.DuplicatorArm.middle => -2
  | .compass OccurrenceSplitRing.Port.southwest => -1
  | .compass OccurrenceSplitRing.Port.northeast => -1
  | _ => 0

/-- Maximum transverse deviation within one primitive inward staircase
block. -/
def retainedTerminalFanOuterTransverseUpperDeviation :
    RetainedTerminalDirection → Int
  | .routedClause PlanarThreeSAT.DuplicatorArm.left => 8
  | .routedClause PlanarThreeSAT.DuplicatorArm.right => 2
  | .routedClause PlanarThreeSAT.DuplicatorArm.middle => 2
  | .compass OccurrenceSplitRing.Port.southeast => 1
  | .compass OccurrenceSplitRing.Port.northwest => 1
  | _ => 0

/-- Each transverse normal annihilates its retained terminal primitive. -/
theorem retainedTerminalFanOuterTransverseNormal_primitive_zero :
    ∀ direction : RetainedTerminalDirection,
      Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal direction)
        direction.primitive = 0 := by
  intro direction
  cases direction with
  | compass port =>
      cases port <;> native_decide
  | routedClause arm =>
      cases arm <;> native_decide

/-- Every clockwise lane step advances strictly in the selected transverse
functional. -/
theorem retainedTerminalFanOuterTransverseNormal_laneStep_positive :
    ∀ direction : RetainedTerminalDirection,
      0 <
        Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          (retainedTerminalFanOuterLaneStep direction) := by
  intro direction
  cases direction with
  | compass port =>
      cases port <;> native_decide
  | routedClause arm =>
      cases arm <;> native_decide

@[simp]
theorem Cell.linearValue_add
    (normal first second : Cell) :
    Cell.linearValue normal (Cell.add first second) =
      Cell.linearValue normal first +
        Cell.linearValue normal second := by
  rcases normal with ⟨normalX, normalY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [Cell.linearValue, Cell.add]
  ring

/-- A repeated diagonal elbow stays in the transverse band of its first
primitive block when a linear functional annihilates the full diagonal
step. -/
theorem diagonalStaircase_linear_bounds
    (normal : Cell) (lower upper horizontal vertical : Int)
    (lowerZero : lower ≤ 0)
    (zeroUpper : 0 ≤ upper)
    (elbowLower :
      lower ≤
        Cell.linearValue normal (horizontal, 0))
    (elbowUpper :
      Cell.linearValue normal (horizontal, 0) ≤ upper)
    (stepZero :
      Cell.linearValue normal (horizontal, vertical) = 0)
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈
        diagonalStaircase horizontal vertical length start) :
    Cell.linearValue normal start + lower ≤
        Cell.linearValue normal point ∧
      Cell.linearValue normal point ≤
        Cell.linearValue normal start + upper := by
  induction length generalizing start point with
  | zero =>
      simp [diagonalStaircase] at pointMember
      subst point
      omega
  | succ length induction =>
      simp only [diagonalStaircase,
        List.mem_cons] at pointMember
      rcases pointMember with
          rfl | rfl | trailingMember
      · omega
      · rw [Cell.linearValue_add]
        omega
      · have trailing :=
          induction
            (Cell.add start (horizontal, vertical))
            point trailingMember
        rw [Cell.linearValue_add, stepZero, add_zero]
          at trailing
        exact trailing

/-- The explicit offsets in every exceptional routed-clause block satisfy
their advertised transverse band. -/
theorem routedClauseRayOffsets_transverse_bounds :
    ∀ (arm : PlanarThreeSAT.DuplicatorArm)
      (offset : Cell),
      offset ∈ routedClauseRayOffsets arm →
        retainedTerminalFanOuterTransverseLowerDeviation
            (.routedClause arm) ≤
          Cell.linearValue
            (retainedTerminalFanOuterTransverseNormal
              (.routedClause arm))
            offset ∧
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (.routedClause arm))
              offset ≤
            retainedTerminalFanOuterTransverseUpperDeviation
              (.routedClause arm) := by
  native_decide

/-- A translated exceptional primitive block has the same transverse
deviation bounds as its finite offset list. -/
theorem routedClauseRayBlock_transverse_bounds
    (arm : PlanarThreeSAT.DuplicatorArm)
    (start point : Cell)
    (pointMember :
      point ∈ routedClauseRayBlock arm start) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          start +
        retainedTerminalFanOuterTransverseLowerDeviation
          (.routedClause arm) ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          point ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          start +
        retainedTerminalFanOuterTransverseUpperDeviation
          (.routedClause arm) := by
  rw [routedClauseRayBlock, List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  rw [Cell.linearValue_add]
  have offsetBounds :=
    routedClauseRayOffsets_transverse_bounds
      arm offset offsetMember
  omega

/-- Repeating an exceptional block preserves its one-block transverse
band, because every block endpoint returns to transverse coordinate zero. -/
theorem routedClauseRay_transverse_bounds
    (arm : PlanarThreeSAT.DuplicatorArm)
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈ routedClauseRay arm length start) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          start +
        retainedTerminalFanOuterTransverseLowerDeviation
          (.routedClause arm) ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          point ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.routedClause arm))
          start +
        retainedTerminalFanOuterTransverseUpperDeviation
          (.routedClause arm) := by
  induction length generalizing start point with
  | zero =>
      simp [routedClauseRay] at pointMember
      subst point
      cases arm <;>
        simp [Cell.linearValue,
          retainedTerminalFanOuterTransverseNormal,
          retainedTerminalFanOuterTransverseLowerDeviation,
          retainedTerminalFanOuterTransverseUpperDeviation] <;>
        omega
  | succ length induction =>
      rw [routedClauseRay] at pointMember
      rcases mem_joinAtEndpoint pointMember with
          blockMember | trailingMember
      · exact routedClauseRayBlock_transverse_bounds
          arm start point blockMember
      · have trailing :=
          induction
            (Cell.add start
              (routedClauseRayPrimitive arm))
            point trailingMember
        have primitiveZero :
            Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (.routedClause arm))
                (routedClauseRayPrimitive arm) = 0 := by
          cases arm <;> native_decide
        rw [Cell.linearValue_add,
          primitiveZero, add_zero] at trailing
        exact trailing

/-- Every inward compass raster stays within its exact one-elbow
transverse band. -/
theorem compassInwardRay_transverse_bounds
    (port : OccurrenceSplitRing.Port)
    (length : Nat) (start point : Cell)
    (pointMember :
      point ∈ compassRay (oppositePort port) length start) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.compass port))
          start +
        retainedTerminalFanOuterTransverseLowerDeviation
          (.compass port) ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.compass port))
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.compass port))
          point ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (.compass port))
          start +
        retainedTerminalFanOuterTransverseUpperDeviation
          (.compass port) := by
  cases length with
  | zero =>
      simp [compassRay] at pointMember
      subst point
      cases port <;>
        simp [Cell.linearValue,
          retainedTerminalFanOuterTransverseNormal,
          retainedTerminalFanOuterTransverseLowerDeviation,
          retainedTerminalFanOuterTransverseUpperDeviation] <;>
        omega
  | succ length =>
      cases port with
      | northwest =>
        exact
          diagonalStaircase_linear_bounds
            (retainedTerminalFanOuterTransverseNormal
              (.compass .northwest))
            (retainedTerminalFanOuterTransverseLowerDeviation
              (.compass .northwest))
            (retainedTerminalFanOuterTransverseUpperDeviation
              (.compass .northwest))
            1 1
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
      | north =>
        simp [compassRay, oppositePort] at pointMember
        rcases pointMember with rfl | rfl
        · simp [retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
        · simp [Cell.linearValue, Cell.add, Cell.scale,
            OccurrenceSplitRing.Port.unitVector,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
      | northeast =>
        exact
          diagonalStaircase_linear_bounds
            (retainedTerminalFanOuterTransverseNormal
              (.compass .northeast))
            (retainedTerminalFanOuterTransverseLowerDeviation
              (.compass .northeast))
            (retainedTerminalFanOuterTransverseUpperDeviation
              (.compass .northeast))
            (-1) 1
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
      | east =>
        simp [compassRay, oppositePort] at pointMember
        rcases pointMember with rfl | rfl
        · simp [retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
        · simp [Cell.linearValue, Cell.add, Cell.scale,
            OccurrenceSplitRing.Port.unitVector,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
      | southeast =>
        exact
          diagonalStaircase_linear_bounds
            (retainedTerminalFanOuterTransverseNormal
              (.compass .southeast))
            (retainedTerminalFanOuterTransverseLowerDeviation
              (.compass .southeast))
            (retainedTerminalFanOuterTransverseUpperDeviation
              (.compass .southeast))
            (-1) (-1)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
      | south =>
        simp [compassRay, oppositePort] at pointMember
        rcases pointMember with rfl | rfl
        · simp [retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
        · simp [Cell.linearValue, Cell.add, Cell.scale,
            OccurrenceSplitRing.Port.unitVector,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
      | southwest =>
        exact
          diagonalStaircase_linear_bounds
            (retainedTerminalFanOuterTransverseNormal
              (.compass .southwest))
            (retainedTerminalFanOuterTransverseLowerDeviation
              (.compass .southwest))
            (retainedTerminalFanOuterTransverseUpperDeviation
              (.compass .southwest))
            1 (-1)
            (by native_decide) (by native_decide)
            (by native_decide) (by native_decide)
            (by native_decide)
            (length + 1) start point
            (by simpa [compassRay, oppositePort] using pointMember)
      | west =>
        simp [compassRay, oppositePort] at pointMember
        rcases pointMember with rfl | rfl
        · simp [retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]
        · simp [Cell.linearValue, Cell.add, Cell.scale,
            OccurrenceSplitRing.Port.unitVector,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseLowerDeviation,
            retainedTerminalFanOuterTransverseUpperDeviation]

/-- The full inward retained-ray raster has an exact transverse band whose
width is independent of its arbitrary length. -/
theorem retainedTerminalFanOuterInwardRay_transverse_bounds
    (direction : RetainedTerminalDirection)
    (terminalLength : Nat)
    (start point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterInwardRay
          (direction, terminalLength)).rasterize start) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          start +
        retainedTerminalFanOuterTransverseLowerDeviation direction ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          point ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          start +
        retainedTerminalFanOuterTransverseUpperDeviation direction := by
  cases direction with
  | compass port =>
      exact compassInwardRay_transverse_bounds
        port
        (retainedTerminalFanOuterRadialLength
          (.compass port, terminalLength))
        start point
        (by simpa [retainedTerminalFanOuterInwardRay,
          RetainedRay.rasterize] using pointMember)
  | routedClause arm =>
      exact routedClauseRay_transverse_bounds
        arm
        (retainedTerminalFanOuterRadialLength
          (.routedClause arm, terminalLength))
        start point
        (by simpa [retainedTerminalFanOuterInwardRay,
          RetainedRay.rasterize] using pointMember)

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

/-- Uniform radial slack covering a lane shift and the radius-nine
rasterization corridor.  Compass primitives need only the smaller bound;
the three exceptional primitives have larger coordinates. -/
def retainedTerminalFanOuterSameDirectionRadialSlack :
    RetainedTerminalDirection → Int
  | .compass _ => 80
  | .routedClause _ => 400

/-- Radial threshold just beyond the gate of the earlier of two nested
same-direction routes. -/
def retainedTerminalFanOuterSameDirectionRadialBound
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (length : Nat) : Int :=
  Cell.linearValue direction.primitive center +
    288 * (length : Int) *
      Cell.linearValue direction.primitive direction.primitive +
    retainedTerminalFanOuterSameDirectionRadialSlack direction

/-- The short lane shift at an earlier gate stays below its radial
threshold. -/
theorem retainedTerminalFanOuterSameDirectionLaneShift_linear_upper
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLaneShiftRouteAt
        (retainedAngularFanOuterDemand
          center (direction, length) slot).gate
        direction slot) :
    Cell.linearValue direction.primitive point ≤
      retainedTerminalFanOuterSameDirectionRadialBound
        center direction length := by
  have gateEq :=
    retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (direction, length) slot
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    subst offset
    rw [gateEq]
    rcases direction with _ | _ <;>
      rename_i kind <;>
      cases kind <;>
      simp [
        retainedTerminalFanOuterSameDirectionRadialBound,
        retainedTerminalFanOuterSameDirectionRadialSlack,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
      omega
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · rw [gateEq]
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSameDirectionRadialBound,
          retainedTerminalFanOuterSameDirectionRadialSlack,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
        omega
    · rw [gateEq]
      have slotLt := slot.isLt
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSameDirectionRadialBound,
          retainedTerminalFanOuterSameDirectionRadialSlack,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
        omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The entire earlier radial route stays below its radial threshold. -/
theorem retainedTerminalFanOuterSameDirectionRadialRoute_linear_upper
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialRoute
        center (direction, length) slot) :
    Cell.linearValue direction.primitive point ≤
      retainedTerminalFanOuterSameDirectionRadialBound
        center direction length := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (direction, length) slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor
              (direction, length))
            (retainedTerminalFanRefinedInterfaceOffset
              direction)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (direction, length) slot
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate direction slot)
      ((retainedTerminalFanOuterInwardRay
        (direction, length)).rasterize
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              direction slot))) at pointMember
  rcases mem_joinAtEndpoint pointMember with
      shiftMember | rasterMember
  · exact
      retainedTerminalFanOuterSameDirectionLaneShift_linear_upper
        center direction length slot point shiftMember
  · rcases
      (retainedTerminalFanOuterInwardRay
        (direction, length)).rasterize_point_near_checkpoint
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              direction slot))
          rasterMember with
      ⟨index, indexLe, nearby⟩
    rw [gateEq] at nearby
    have coordinateBounds := nearby.coordinate_bounds
    have slotLt := slot.isLt
    rcases direction with _ | _ <;>
      rename_i kind <;>
      cases kind <;>
      simp [
        retainedTerminalFanOuterSameDirectionRadialBound,
        retainedTerminalFanOuterSameDirectionRadialSlack,
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
        RetainedTerminalDirection.primitive,
        oppositePort,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
        at indexLe coordinateBounds ⊢ <;>
      omega

/-- A lane shift at a strictly farther same-direction gate lies beyond the
earlier gate's radial threshold. -/
theorem retainedTerminalFanOuterSameDirectionLaneShift_linear_lower
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (slot : RetainedTerminalSlot)
    (lengthsLt : firstLength < secondLength)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLaneShiftRouteAt
        (retainedAngularFanOuterDemand
          center (direction, secondLength) slot).gate
        direction slot) :
    retainedTerminalFanOuterSameDirectionRadialBound
        center direction firstLength <
      Cell.linearValue direction.primitive point := by
  have gateEq :=
    retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (direction, secondLength) slot
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    subst offset
    rw [gateEq]
    rcases direction with _ | _ <;>
      rename_i kind <;>
      cases kind <;>
      simp [
        retainedTerminalFanOuterSameDirectionRadialBound,
        retainedTerminalFanOuterSameDirectionRadialSlack,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        Cell.linearValue, Cell.add, Cell.scale, Cell.sub] at lengthsLt ⊢ <;>
      omega
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · rw [gateEq]
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSameDirectionRadialBound,
          retainedTerminalFanOuterSameDirectionRadialSlack,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub] at lengthsLt ⊢ <;>
        omega
    · rw [gateEq]
      have slotLt := slot.isLt
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSameDirectionRadialBound,
          retainedTerminalFanOuterSameDirectionRadialSlack,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub] at lengthsLt ⊢ <;>
        omega

/-- Transverse threshold at the outer edge of one parallel radial lane. -/
def retainedTerminalFanOuterSameDirectionTransverseBound
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : Int :=
  Cell.linearValue
      (retainedTerminalFanOuterTransverseNormal direction)
      center +
    (retainedTerminalFanOuterLaneSpacing * slot.val : Nat) *
      Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal direction)
        (retainedTerminalFanOuterLaneStep direction) +
    retainedTerminalFanOuterTransverseUpperDeviation direction

set_option maxHeartbeats 2000000 in
/-- Every point of a radial route lies below the outer transverse edge of
its own lane band. -/
theorem retainedTerminalFanOuterSameDirectionRadialRoute_transverse_upper
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialRoute
        center (direction, length) slot) :
    Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal direction)
        point ≤
      retainedTerminalFanOuterSameDirectionTransverseBound
        center direction slot := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (direction, length) slot).gate
  have gateEq :
      gate =
        Cell.add center
          (Cell.scale
            (retainedTerminalInterfaceRadialFactor
              (direction, length))
            (retainedTerminalFanRefinedInterfaceOffset
              direction)) := by
    exact retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (direction, length) slot
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate direction slot)
      ((retainedTerminalFanOuterInwardRay
        (direction, length)).rasterize
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              direction slot))) at pointMember
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
      rcases direction with _ | _ <;>
        rename_i kind <;>
        cases kind <;>
        simp [
          retainedTerminalFanOuterSameDirectionTransverseBound,
          retainedTerminalFanOuterTransverseNormal,
          retainedTerminalFanOuterTransverseUpperDeviation,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          routedClauseRayPrimitive,
          Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
        omega
    · simp [retainedTerminalFanOuterLaneShiftRoute,
        slotZero] at offsetMember
      rcases offsetMember with rfl | rfl
      · rw [gateEq]
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          simp [
            retainedTerminalFanOuterSameDirectionTransverseBound,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseUpperDeviation,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            RetainedTerminalDirection.primitive,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
          omega
      · rw [gateEq]
        rcases direction with _ | _ <;>
          rename_i kind <;>
          cases kind <;>
          simp [
            retainedTerminalFanOuterSameDirectionTransverseBound,
            retainedTerminalFanOuterTransverseNormal,
            retainedTerminalFanOuterTransverseUpperDeviation,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalInterfaceRadialFactor,
            retainedTerminalFanRefinedInterfaceOffset,
            retainedTerminalInterfaceOffset,
            retainedTerminalInterfaceMultiplier,
            retainedTerminalFanRoutingRefinement,
            RetainedTerminalDirection.primitive,
            OccurrenceSplitRing.Port.unitVector,
            routedClauseRayPrimitive,
            Cell.linearValue, Cell.add, Cell.scale, Cell.sub] <;>
          omega
  · have transverse :=
      retainedTerminalFanOuterInwardRay_transverse_bounds
        direction length
        (Cell.add gate
          (retainedTerminalFanOuterLaneOffset direction slot))
        point rasterMember
    rw [gateEq] at transverse
    rcases direction with _ | _ <;>
      rename_i kind <;>
      cases kind <;>
      simp [
        retainedTerminalFanOuterSameDirectionTransverseBound,
        retainedTerminalFanOuterTransverseNormal,
        retainedTerminalFanOuterTransverseUpperDeviation,
        retainedTerminalFanOuterLaneOffset,
        retainedTerminalFanOuterLaneStep,
        retainedTerminalFanOuterLaneSpacing,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
        at transverse ⊢ <;>
      omega

/-- The raster of a strictly later parallel lane lies beyond the earlier
lane's transverse threshold. -/
theorem retainedTerminalFanOuterSameDirectionInwardRay_transverse_lower
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsLt : firstSlot.val < secondSlot.val)
    (point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterInwardRay
          (direction, length)).rasterize
          (Cell.add
            (retainedAngularFanOuterDemand
              center (direction, length) secondSlot).gate
            (retainedTerminalFanOuterLaneOffset
              direction secondSlot))) :
    retainedTerminalFanOuterSameDirectionTransverseBound
        center direction firstSlot <
      Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal direction)
        point := by
  have gateEq :=
    retainedAngularFanOuterDemand_gate_eq_interface_ray
      center (direction, length) secondSlot
  have transverse :=
    retainedTerminalFanOuterInwardRay_transverse_bounds
      direction length
      (Cell.add
        (retainedAngularFanOuterDemand
          center (direction, length) secondSlot).gate
        (retainedTerminalFanOuterLaneOffset
          direction secondSlot))
      point pointMember
  rw [gateEq] at transverse
  rcases direction with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [
      retainedTerminalFanOuterSameDirectionTransverseBound,
      retainedTerminalFanOuterTransverseNormal,
      retainedTerminalFanOuterTransverseLowerDeviation,
      retainedTerminalFanOuterTransverseUpperDeviation,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanOuterLaneSpacing,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive,
      OccurrenceSplitRing.Port.unitVector,
      routedClauseRayPrimitive,
      Cell.linearValue, Cell.add, Cell.scale, Cell.sub]
      at transverse ⊢ <;>
    omega

/-- Nested radial routes in one retained direction are continuously
separated: radial progress separates the farther route's entrance, and
the exact transverse bands separate its parallel inward raster. -/
theorem retainedTerminalFanOuterRadialRoutes_strictlyAvoid_of_direction_eq
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthsLt : firstLength < secondLength)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center (direction, firstLength) firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center (direction, secondLength) secondSlot) := by
  let secondGate :=
    (retainedAngularFanOuterDemand
      center (direction, secondLength) secondSlot).gate
  have avoidsShift :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterRadialRoute
          center (direction, firstLength) firstSlot)
        (retainedTerminalFanOuterLaneShiftRouteAt
          secondGate direction secondSlot) :=
    routesStrictlyAvoidEachOther_of_linear_separated
      direction.primitive
      (retainedTerminalFanOuterSameDirectionRadialBound
        center direction firstLength)
      (retainedTerminalFanOuterSameDirectionRadialRoute_linear_upper
        center direction firstLength firstSlot)
      (retainedTerminalFanOuterSameDirectionLaneShift_linear_lower
        center direction firstLength secondLength secondSlot
        lengthsLt)
  have avoidsRaster :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterRadialRoute
          center (direction, firstLength) firstSlot)
        ((retainedTerminalFanOuterInwardRay
          (direction, secondLength)).rasterize
            (Cell.add secondGate
              (retainedTerminalFanOuterLaneOffset
                direction secondSlot))) :=
    routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterTransverseNormal direction)
      (retainedTerminalFanOuterSameDirectionTransverseBound
        center direction firstSlot)
      (retainedTerminalFanOuterSameDirectionRadialRoute_transverse_upper
        center direction firstLength firstSlot)
      (retainedTerminalFanOuterSameDirectionInwardRay_transverse_lower
        center direction secondLength firstSlot secondSlot slotsLt)
  rw [retainedTerminalFanOuterRadialRoute]
  change RoutesStrictlyAvoidEachOther
    (retainedTerminalFanOuterRadialRoute
      center (direction, firstLength) firstSlot)
    (joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        secondGate direction secondSlot)
      ((retainedTerminalFanOuterInwardRay
        (direction, secondLength)).rasterize
          (Cell.add secondGate
            (retainedTerminalFanOuterLaneOffset
              direction secondSlot))))
  exact avoidsShift.join_right avoidsRaster
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      secondGate direction secondSlot)
    (RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardRay
        (direction, secondLength))
      (Cell.add secondGate
        (retainedTerminalFanOuterLaneOffset
          direction secondSlot)))

/-- Radial routes are separated whenever their direction ranks and slots
are ordered, using radial tie-breaking in the equal-direction case. -/
theorem retainedTerminalFanOuterRadialRoutes_strictlyAvoid
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤
        secondDirection.angularRank)
    (firstLengthPositive : 0 < firstLength)
    (secondLengthPositive : 0 < secondLength)
    (equalDirectionLengthsLt :
      firstDirection = secondDirection →
        firstLength < secondLength)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center (firstDirection, firstLength) firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center (secondDirection, secondLength) secondSlot) := by
  rcases lt_or_eq_of_le directionsLe with
      directionsLt | ranksEqual
  · exact
      retainedTerminalFanOuterRadialRoutes_strictlyAvoid_of_direction_lt
        center firstDirection secondDirection
        firstLength secondLength firstSlot secondSlot
        directionsLt firstLengthPositive secondLengthPositive slotsLt
  · have directionsEqual :
        firstDirection = secondDirection :=
      RetainedTerminalDirection.angularRank_injective ranksEqual
    subst secondDirection
    exact
      retainedTerminalFanOuterRadialRoutes_strictlyAvoid_of_direction_eq
        center firstDirection firstLength secondLength
        firstSlot secondSlot
        (equalDirectionLengthsLt rfl) slotsLt

/-- A duplicate-free angular terminal profile supplies every hypothesis
needed to separate the radial routes selected by two ordered active slots. -/
theorem RetainedAngularTerminalProfile.outerRadialRoutes_strictlyAvoid
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (center : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstLookup :
      profile.terminals[firstSlot.val]? = some firstTerminal)
    (secondLookup :
      profile.terminals[secondSlot.val]? = some secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterRadialRoute
        center secondTerminal secondSlot) := by
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstLt, firstEq⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondLt, secondEq⟩
  have directionsLe :
      firstTerminal.1.angularRank ≤
        secondTerminal.1.angularRank := by
    have ordered :=
      (List.pairwise_iff_getElem.mp profile.rankSorted)
        firstSlot.val secondSlot.val
        firstLt secondLt slotsLt
    simpa [firstEq, secondEq] using ordered
  have equalDirectionLengthsLt :
      firstTerminal.1 = secondTerminal.1 →
        firstTerminal.2 < secondTerminal.2 := by
    intro directionsEqual
    have concreteDirectionsEqual :
        (profile.terminals[firstSlot.val]'firstLt).1 =
          (profile.terminals[secondSlot.val]'secondLt).1 := by
      simpa [firstEq, secondEq] using directionsEqual
    have lengthsLt :=
      profile.length_lt_of_lt_of_direction_eq distinct
        firstSlot.val secondSlot.val
        firstLt secondLt slotsLt concreteDirectionsEqual
    simpa [firstEq, secondEq] using lengthsLt
  exact retainedTerminalFanOuterRadialRoutes_strictlyAvoid
    center firstTerminal.1 secondTerminal.1
    firstTerminal.2 secondTerminal.2
    firstSlot secondSlot directionsLe
    (profile.length_positive_of_lookup
      firstSlot firstTerminal firstLookup)
    (profile.length_positive_of_lookup
      secondSlot secondTerminal secondLookup)
    equalDirectionLengthsLt slotsLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes
