import LeanTrominoes.OrthogonalPolylineLinearSeparation
import LeanTrominoes.RetainedAngularFanOuterCoordinatedSeparation
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-!
# Cardinal half-plane bounds after a source escape

For a cardinal terminal, the first 64 blocks of the escaped outer route
move directly inward.  The occurrence-lane shift is perpendicular to that
direction, and every later radial point moves farther inward.  The finite
local fan also lies well inside the same threshold once the source terminal
has length at least two.

This file packages that observation as a pointwise linear bound on the
complete tail after the escape checkpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- After a 64-block escape on a cardinal terminal of length at least two,
the whole remaining complete fan lies strictly inward of the source gate. -/
theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail_cardinal_linear_upper
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          center (.compass port, length) slot) :
    Cell.linearValue port.unitVector point ≤
      Cell.linearValue port.unitVector
          (retainedAngularFanOuterDemand
            center (.compass port, length) slot).gate -
        retainedTerminalFanOuterSourceEscapeLength := by
  let terminal : RetainedTerminalData :=
    (.compass port, length)
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint
      center terminal slot
  change
    Cell.linearValue port.unitVector point ≤
      Cell.linearValue port.unitVector gate -
        retainedTerminalFanOuterSourceEscapeLength
  have escapePointLinear :
      Cell.linearValue port.unitVector escapePoint =
        Cell.linearValue port.unitVector gate -
          retainedTerminalFanOuterSourceEscapeLength := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [escapePoint, gate, terminal,
        retainedTerminalFanOuterSourceEscapePoint,
        retainedTerminalFanOuterSourceEscapeRay,
        retainedTerminalFanOuterInwardRayOfLength,
        retainedTerminalFanOuterSourceEscapeLength,
        RetainedRay.vector, oppositePort,
        Port.unitVector, Cell.linearValue,
        Cell.add, Cell.scale] <;>
      ring
  rw [retainedTerminalFanOuterCoordinatedEscapedCompleteTail]
    at pointMember
  rcases mem_joinAtEndpoint pointMember with
    shiftedMember | localMember
  · rw [retainedTerminalFanOuterEscapedShiftedTail]
      at shiftedMember
    change
      point ∈
        joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            escapePoint terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
            (Cell.add escapePoint
              (retainedTerminalFanOuterLaneOffset terminal.1 slot)))
      at shiftedMember
    rcases mem_joinAtEndpoint shiftedMember with
      shiftMember | remainingMember
    · unfold retainedTerminalFanOuterLaneShiftRouteAt
        PeriodicOrthocrossing.translatePolyline at shiftMember
      rw [List.mem_map] at shiftMember
      rcases shiftMember with ⟨offset, offsetMember, rfl⟩
      by_cases slotZero : slot.val = 0
      · simp [retainedTerminalFanOuterLaneShiftRoute,
          slotZero] at offsetMember
        subst offset
        simpa [Cell.linearValue, Cell.add] using
          escapePointLinear.le
      · simp [retainedTerminalFanOuterLaneShiftRoute,
          slotZero] at offsetMember
        rcases offsetMember with rfl | rfl
        · simpa [Cell.linearValue, Cell.add] using
            escapePointLinear.le
        · rcases cardinal with rfl | rfl | rfl | rfl <;>
            simp [terminal,
              retainedTerminalFanOuterLaneOffset,
              retainedTerminalFanOuterLaneStep,
              retainedTerminalFanOuterLaneSpacing,
              Port.unitVector, Cell.linearValue,
              Cell.add, Cell.scale] at escapePointLinear ⊢ <;>
            omega
    · have remainingPositive :
          0 <
            retainedTerminalFanOuterRadialLength terminal -
              retainedTerminalFanOuterSourceEscapeLength := by
        simp [terminal, retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanTotalRefinement_eq,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier]
        omega
      have remainingPair :
          (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
              (Cell.add escapePoint
                (retainedTerminalFanOuterLaneOffset terminal.1 slot)) =
            [Cell.add escapePoint
                (retainedTerminalFanOuterLaneOffset terminal.1 slot),
              Cell.add
                (Cell.add escapePoint
                  (retainedTerminalFanOuterLaneOffset terminal.1 slot))
                (Cell.scale
                  ((retainedTerminalFanOuterRadialLength terminal -
                    retainedTerminalFanOuterSourceEscapeLength : Nat) : Int)
                  (oppositePort port).unitVector)] := by
        have oppositeCardinal :
            oppositePort port = .north ∨
              oppositePort port = .east ∨
              oppositePort port = .south ∨
              oppositePort port = .west := by
          rcases cardinal with rfl | rfl | rfl | rfl <;>
            simp [oppositePort]
        simpa [terminal,
          retainedTerminalFanOuterEscapedRemainingRay,
          retainedTerminalFanOuterInwardRayOfLength,
          RetainedRay.rasterize] using
            (compassRay_eq_pair_of_cardinal
              (oppositePort port)
              (retainedTerminalFanOuterRadialLength terminal -
                retainedTerminalFanOuterSourceEscapeLength)
              remainingPositive
              (Cell.add escapePoint
                (retainedTerminalFanOuterLaneOffset terminal.1 slot))
              oppositeCardinal)
      rw [remainingPair] at remainingMember
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at remainingMember
      rcases remainingMember with rfl | rfl
      · rcases cardinal with rfl | rfl | rfl | rfl <;>
          simp [terminal, gate,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            Port.unitVector, Cell.linearValue,
            Cell.add, Cell.scale] at escapePointLinear ⊢ <;>
          omega
      · rcases cardinal with rfl | rfl | rfl | rfl <;>
          simp [terminal, gate,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            retainedTerminalFanOuterRadialLength,
            retainedTerminalFanOuterSourceEscapeLength,
            retainedTerminalFanTotalRefinement_eq,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalInterfaceMultiplier,
            oppositePort, Port.unitVector,
            Cell.linearValue, Cell.add, Cell.scale]
            at escapePointLinear ⊢ <;>
          omega
  · rw [retainedTerminalFanOuterLocalRouteAt,
      List.mem_map] at localMember
    rcases localMember with
      ⟨offset, offsetMember, rfl⟩
    have offsetBounded :=
      retainedTerminalFanOuterLocalRoute_points_within_outer_frame
        terminal.1 slot offset offsetMember
    have coordinateBounds := offsetBounded.coordinate_bounds
    have gateEq :
        gate =
          Cell.add center
            (Cell.scale
              (retainedTerminalInterfaceRadialFactor terminal)
              (retainedTerminalFanRefinedInterfaceOffset terminal.1)) := by
      simpa [gate] using
        (retainedAngularFanOuterDemand_gate_eq_interface_ray
          center terminal slot)
    rw [gateEq]
    rcases center with ⟨centerX, centerY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [terminal,
        retainedTerminalInterfaceRadialFactor,
        retainedTerminalFanRefinedInterfaceOffset,
        retainedTerminalInterfaceOffset,
        retainedTerminalInterfaceMultiplier,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalFanOuterSourceEscapeLength,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        Port.unitVector, Cell.linearValue,
        Cell.add, Cell.scale] at coordinateBounds ⊢ <;>
      omega

/-- A route that stays on or beyond a cardinal source gate is strictly
separated from the complete fan tail after the 64-block escape. -/
theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail_strictlyAvoid_of_cardinal_of_linear_lower
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (other : List Cell)
    (otherLower :
      ∀ point ∈ other,
        Cell.linearValue port.unitVector
            (retainedAngularFanOuterDemand
              center (.compass port, length) slot).gate ≤
          Cell.linearValue port.unitVector point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
        center (.compass port, length) slot)
      other := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    port.unitVector
    (Cell.linearValue port.unitVector
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate -
      retainedTerminalFanOuterSourceEscapeLength)
  · intro point pointMember
    exact
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_cardinal_linear_upper
        center port length slot cardinal lengthLarge point pointMember
  · intro point pointMember
    have lower := otherLower point pointMember
    simp [retainedTerminalFanOuterSourceEscapeLength]
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
