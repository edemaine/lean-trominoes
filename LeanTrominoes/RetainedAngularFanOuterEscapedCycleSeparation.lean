/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterCycleSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes

/-!
# Separating escaped outer fan routes from the inner implication cycle

The delayed-lane fallback follows the same supporting side as an ordinary
outer radial route: its initial escape raster moves inward, its lane shift
is tangential to the selected side, and its remaining raster ends at the
same radius-288 lane port.  Consequently the entire escaped radial route
stays weakly beyond that supporting line.

Combining this arbitrary-length bound with the finite local certificate
proves that a complete escaped outer fan is strictly contact-free from
every implication route in its own radius-48 Figure 7 cycle.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- An inward raster of any specified length moves monotonically toward
the selected supporting side. -/
theorem retainedTerminalFanOuterInwardRayOfLength_side_ge_finish
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (start point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterInwardRayOfLength
          direction length).rasterize start) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        (Cell.add start
          (retainedTerminalFanOuterInwardRayOfLength
            direction length).vector) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        point := by
  cases direction with
  | compass port =>
      exact compassInwardRay_side_ge_finish
        port length start point
        (by simpa [retainedTerminalFanOuterInwardRayOfLength,
          RetainedRay.rasterize, RetainedRay.vector]
          using pointMember)
  | routedClause arm =>
      exact routedClauseRay_side_ge_finish
        arm length start point
        (by simpa [retainedTerminalFanOuterInwardRayOfLength,
          RetainedRay.rasterize, RetainedRay.vector]
          using pointMember)

/-- Every occurrence-lane displacement is tangential to its direction's
selected supporting side. -/
theorem retainedTerminalFanOuterLaneOffset_side_zero :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        (retainedTerminalFanOuterLaneOffset direction slot) = 0 := by
  intro direction slot
  rcases direction with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    revert slot <;>
    native_decide

/-- Every point of a translated lane shift has the same supporting-side
value as its start. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_side_eq
    (start : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterLaneShiftRouteAt
        start direction slot) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        point =
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        start := by
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  by_cases slotZero : slot.val = 0
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    subst offset
    simp
  · simp [retainedTerminalFanOuterLaneShiftRoute,
      slotZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · simp
    · rw [Cell.linearValue_add,
        retainedTerminalFanOuterLaneOffset_side_zero]
      omega

/-- The remaining raster of a fitting escaped route ends at the ordinary
radius-288 lane port. -/
theorem retainedTerminalFanOuterEscapedRemaining_finish_eq_lanePort
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    Cell.add
        (Cell.add
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot)
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
      retainedTerminalFanOuterLanePort
        center terminal.1 slot := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  have ordinaryLast :=
    retainedTerminalFanOuterInwardRay_getLast?
      center terminal slot lengthPositive
  rw [RetainedRay.rasterize_getLast?] at ordinaryLast
  change
    Cell.add
        (Cell.add
          (Cell.add gate
            (retainedTerminalFanOuterSourceEscapeRay terminal).vector)
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
      retainedTerminalFanOuterLanePort center terminal.1 slot
  calc
    Cell.add
        (Cell.add
          (Cell.add gate
            (retainedTerminalFanOuterSourceEscapeRay terminal).vector)
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
      Cell.add
        (Cell.add gate
          (retainedTerminalFanOuterLaneOffset terminal.1 slot))
        (retainedTerminalFanOuterInwardRay terminal).vector := by
        rw [← retainedTerminalFanOuterEscapedRay_vectors_add
          terminal escapeFits]
        rcases gate with ⟨gateX, gateY⟩
        rcases
            (retainedTerminalFanOuterSourceEscapeRay terminal).vector with
          ⟨escapeX, escapeY⟩
        rcases
            (retainedTerminalFanOuterEscapedRemainingRay terminal).vector with
          ⟨remainingX, remainingY⟩
        rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
          ⟨offsetX, offsetY⟩
        apply Prod.ext <;>
          simp [Cell.add] <;>
          ring
    _ = retainedTerminalFanOuterLanePort
          center terminal.1 slot :=
      Option.some.inj ordinaryLast

/-- Every point of the remaining escaped raster lies weakly beyond the
radius-288 supporting side. -/
theorem retainedTerminalFanOuterEscapedRemainingRay_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot)
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  have outward :=
    retainedTerminalFanOuterInwardRayOfLength_side_ge_finish
      terminal.1
      (retainedTerminalFanOuterRadialLength terminal -
        retainedTerminalFanOuterSourceEscapeLength)
      (Cell.add
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot)
        (retainedTerminalFanOuterLaneOffset terminal.1 slot))
      point
      (by simpa [retainedTerminalFanOuterEscapedRemainingRay]
        using pointMember)
  have finishEq :=
    retainedTerminalFanOuterEscapedRemaining_finish_eq_lanePort
      center terminal slot lengthPositive escapeFits
  change
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        (Cell.add
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot)
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))
          (retainedTerminalFanOuterEscapedRemainingRay terminal).vector) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point
    at outward
  rw [finishEq, retainedTerminalFanOuterLanePort,
    Cell.linearValue_add,
    retainedTerminalFanOuterSideNormal_lanePortOffset]
    at outward
  exact outward

/-- The point at which the escaped route selects its occurrence lane lies
weakly beyond the radius-288 supporting side. -/
theorem retainedTerminalFanOuterSourceEscapePoint_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot) := by
  have shiftedBound :=
    retainedTerminalFanOuterEscapedRemainingRay_side_lower
      center terminal slot lengthPositive escapeFits
      (Cell.add
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot)
        (retainedTerminalFanOuterLaneOffset terminal.1 slot))
      (List.mem_of_mem_head?
        (RetainedRay.rasterize_head?
          (retainedTerminalFanOuterEscapedRemainingRay terminal)
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint
              center terminal slot)
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))))
  rw [Cell.linearValue_add,
    retainedTerminalFanOuterLaneOffset_side_zero] at shiftedBound
  omega

/-- Every point of the initial source-escape raster lies weakly beyond the
radius-288 supporting side. -/
theorem retainedTerminalFanOuterSourceEscapeRay_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈
        (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          (retainedAngularFanOuterDemand
            center terminal slot).gate) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  have outward :=
    retainedTerminalFanOuterInwardRayOfLength_side_ge_finish
      terminal.1 retainedTerminalFanOuterSourceEscapeLength
      (retainedAngularFanOuterDemand center terminal slot).gate
      point
      (by simpa [retainedTerminalFanOuterSourceEscapeRay]
        using pointMember)
  have escapePointBound :=
    retainedTerminalFanOuterSourceEscapePoint_side_lower
      center terminal slot lengthPositive escapeFits
  change
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point
    at outward
  omega

/-- Every point of a fitting escaped radial route lies weakly beyond the
radius-288 supporting side. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterEscapedRadialRoute
        center terminal slot) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  rw [retainedTerminalFanOuterEscapedRadialRoute] at pointMember
  rcases mem_joinAtEndpoint pointMember with
      escapeMember | shiftedTailMember
  · exact retainedTerminalFanOuterSourceEscapeRay_side_lower
      center terminal slot lengthPositive escapeFits
      point escapeMember
  · rcases mem_joinAtEndpoint shiftedTailMember with
        shiftMember | remainingMember
    · have shiftEq :=
        retainedTerminalFanOuterLaneShiftRouteAt_side_eq
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot)
          terminal.1 slot point shiftMember
      have escapePointBound :=
        retainedTerminalFanOuterSourceEscapePoint_side_lower
          center terminal slot lengthPositive escapeFits
      omega
    · exact retainedTerminalFanOuterEscapedRemainingRay_side_lower
        center terminal slot lengthPositive escapeFits
        point remainingMember

/-- A fitting escaped radial route strictly avoids every implication route
in the radius-48 inner square. -/
theorem
    retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : OccurrenceSplitRing.RingVertex)
    (literalIndex : Fin 2)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 48)
      (retainedTerminalFanInnerCycleRouteAt_side_upper
        center terminal.1 vertex literalIndex)
      (fun point pointMember => by
        have outer :=
          retainedTerminalFanOuterEscapedRadialRoute_side_lower
            center terminal slot lengthPositive escapeFits
            point pointMember
        omega)).symm

/-- A fitting complete escaped source-to-Figure-7 fan route strictly avoids
every implication route in its own inner cycle. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_innerCycleRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (vertex : OccurrenceSplitRing.RingVertex)
    (literalIndex : Fin 2)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center terminal slot)
      (retainedTerminalFanInnerCycleRouteAt
        center vertex literalIndex) := by
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  exact
    (retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_innerCycleRouteAt
      center terminal slot vertex literalIndex
      lengthPositive escapeFits).join_left
      (retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_innerCycleRouteAt
        center terminal.1 slot vertex literalIndex)
      (retainedTerminalFanOuterEscapedRadialRoute_getLast?
        center terminal slot lengthPositive escapeFits)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
