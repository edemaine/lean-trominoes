import LeanTrominoes.RetainedRayRasterizationSplitting
import LeanTrominoes.RetainedAngularFanOuterCrossSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedCycleSeparation

/-!
# Cross-separation for escaped radial and local fan routes

The first 64 blocks and delayed lane shift of an escaped radial route lie
strictly outside the radius-288 fan frame whenever a nonempty radial suffix
remains.  The suffix itself is a geometric tail of the corresponding
ordinary radial route, so it inherits the ordinary radial/local separation
theorem.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Every positive inward retained-ray vector advances strictly toward the
interior of its direction's supporting side. -/
theorem retainedTerminalFanOuterInwardRayOfLength_vector_side_negative
    (direction : RetainedTerminalDirection)
    (length : Nat)
    (lengthPositive : 0 < length) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal direction)
        (retainedTerminalFanOuterInwardRayOfLength
          direction length).vector < 0 := by
  rcases direction with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterInwardRayOfLength,
      retainedTerminalFanOuterSideNormal,
      RetainedRay.vector, oppositePort,
      OccurrenceSplitRing.Port.unitVector,
      routedClauseRayPrimitive,
      Cell.linearValue, Cell.scale] at lengthPositive ⊢ <;>
    omega

/-- If the fixed escape leaves a nonempty radial suffix, its endpoint is
strictly outside the radius-288 supporting side. -/
theorem retainedTerminalFanOuterSourceEscapePoint_side_strict_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot) := by
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal :=
    Nat.le_of_lt escapeStrict
  have finishEq :=
    retainedTerminalFanOuterEscapedRemaining_finish_eq_lanePort
      center terminal slot lengthPositive escapeFits
  have remainingPositive :
      0 <
        retainedTerminalFanOuterRadialLength terminal -
          retainedTerminalFanOuterSourceEscapeLength := by
    omega
  have remainingNegative :=
    retainedTerminalFanOuterInwardRayOfLength_vector_side_negative
      terminal.1
      (retainedTerminalFanOuterRadialLength terminal -
        retainedTerminalFanOuterSourceEscapeLength)
      remainingPositive
  change
    Cell.linearValue
      (retainedTerminalFanOuterSideNormal terminal.1)
      (retainedTerminalFanOuterEscapedRemainingRay terminal).vector < 0
    at remainingNegative
  have finishLinear :=
    congrArg
      (Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1))
      finishEq
  rw [Cell.linearValue_add, Cell.linearValue_add,
    retainedTerminalFanOuterLaneOffset_side_zero,
    retainedTerminalFanOuterLanePort,
    Cell.linearValue_add,
    retainedTerminalFanOuterSideNormal_lanePortOffset]
    at finishLinear
  omega

/-- Every point of the initial source-escape raster is strictly outside the
radius-288 supporting side when a nonempty suffix remains. -/
theorem retainedTerminalFanOuterSourceEscapeRay_side_strict_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
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
        288 <
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
  change
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot) ≤
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point
    at outward
  have escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint_side_strict_lower
      center terminal slot lengthPositive escapeStrict
  omega

/-- Every point of the delayed lane shift is strictly outside the
radius-288 supporting side when a nonempty suffix remains. -/
theorem retainedTerminalFanOuterDelayedLaneShift_side_strict_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot)
          terminal.1 slot) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  have shiftEq :=
    retainedTerminalFanOuterLaneShiftRouteAt_side_eq
      (retainedTerminalFanOuterSourceEscapePoint
        center terminal slot)
      terminal.1 slot point pointMember
  have escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint_side_strict_lower
      center terminal slot lengthPositive escapeStrict
  omega

/-- The shifted remaining raster of an escaped route inherits strict
separation from the full inward raster of the ordinary radial route. -/
theorem
    retainedTerminalFanOuterEscapedRemaining_strictlyAvoid_of_inward
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (other : List Cell)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (inwardAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterInwardRay terminal).rasterize
          (Cell.add
            (retainedAngularFanOuterDemand
              center terminal slot).gate
            (retainedTerminalFanOuterLaneOffset
              terminal.1 slot)))
        other) :
    RoutesStrictlyAvoidEachOther
      ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
        (Cell.add
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot)
          (retainedTerminalFanOuterLaneOffset
            terminal.1 slot)))
      other := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate :=
    Cell.add gate
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let remainingLength :=
    retainedTerminalFanOuterRadialLength terminal -
      retainedTerminalFanOuterSourceEscapeLength
  have lengthSplit :
      retainedTerminalFanOuterSourceEscapeLength + remainingLength =
        retainedTerminalFanOuterRadialLength terminal := by
    dsimp [remainingLength]
    omega
  have fullAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterInwardRayOfLength terminal.1
          (retainedTerminalFanOuterSourceEscapeLength +
            remainingLength)).rasterize shiftedGate)
        other := by
    rw [lengthSplit]
    rcases terminal with ⟨direction, terminalLength⟩
    cases direction <;>
      simpa [shiftedGate, gate,
        retainedTerminalFanOuterInwardRay,
        retainedTerminalFanOuterInwardRayOfLength] using inwardAvoid
  have suffixAvoid :=
    retainedTerminalFanOuterInwardRayOfLength_suffix_strictlyAvoid
      terminal.1 retainedTerminalFanOuterSourceEscapeLength
      remainingLength shiftedGate other
      (by simp [retainedTerminalFanOuterSourceEscapeLength])
      fullAvoid
  have checkpointEq :
      Cell.add shiftedGate
          (Cell.scale retainedTerminalFanOuterSourceEscapeLength
            (retainedTerminalFanOuterInwardRayOfLength terminal.1
              retainedTerminalFanOuterSourceEscapeLength).primitive) =
        Cell.add
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot)
          (retainedTerminalFanOuterLaneOffset
            terminal.1 slot) := by
    unfold retainedTerminalFanOuterSourceEscapePoint
      retainedTerminalFanOuterSourceEscapeRay
    rw [RetainedRay.vector_eq_scale_length_primitive]
    have sourceLength :
        (retainedTerminalFanOuterInwardRayOfLength terminal.1
          retainedTerminalFanOuterSourceEscapeLength).length =
            retainedTerminalFanOuterSourceEscapeLength := by
      rcases terminal with ⟨direction, terminalLength⟩
      cases direction <;>
        rfl
    rw [sourceLength]
    apply Prod.ext <;>
      simp [shiftedGate, gate,
        retainedTerminalFanOuterInwardRayOfLength,
        RetainedRay.primitive,
        Cell.add, Cell.scale] <;>
      ring
  simpa [remainingLength,
    retainedTerminalFanOuterEscapedRemainingRay,
    checkpointEq] using suffixAvoid

/-- Whenever an ordinary radial route strictly avoids a local adapter, its
escaped version also avoids that adapter, provided the fixed escape leaves
a nonempty suffix. -/
theorem
    retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_local_of_radial
    (center : Cell)
    (terminal : RetainedTerminalData)
    (radialSlot localSlot : RetainedTerminalSlot)
    (localDirection : RetainedTerminalDirection)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (radialAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterRadialRoute
          center terminal radialSlot)
        (retainedTerminalFanOuterLocalRouteAt
          center localDirection localSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal radialSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center localDirection localSlot) := by
  let gate :=
    (retainedAngularFanOuterDemand
      center terminal radialSlot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint
      center terminal radialSlot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset
        terminal.1 radialSlot)
  let localRoute :=
    retainedTerminalFanOuterLocalRouteAt
      center localDirection localSlot
  have sourceAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate)
        localRoute :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 288)
      (retainedTerminalFanOuterLocalRouteAt_side_upper
        center terminal.1 localDirection localSlot)
      (retainedTerminalFanOuterSourceEscapeRay_side_strict_lower
        center terminal radialSlot lengthPositive escapeStrict)).symm
  have shiftAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterLaneShiftRouteAt
          escapePoint terminal.1 radialSlot)
        localRoute :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 288)
      (retainedTerminalFanOuterLocalRouteAt_side_upper
        center terminal.1 localDirection localSlot)
      (retainedTerminalFanOuterDelayedLaneShift_side_strict_lower
        center terminal radialSlot lengthPositive escapeStrict)).symm
  have inwardAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterInwardRay terminal).rasterize
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              terminal.1 radialSlot)))
        localRoute := by
    rw [retainedTerminalFanOuterRadialRoute] at radialAvoid
    exact
      (radialAvoid.of_join_left
        (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
          gate terminal.1 radialSlot)
        (RetainedRay.rasterize_head? _ _)).2
  have remainingAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          shiftedEscapePoint)
        localRoute := by
    simpa [shiftedEscapePoint, escapePoint, gate, localRoute] using
      retainedTerminalFanOuterEscapedRemaining_strictlyAvoid_of_inward
        center terminal radialSlot localRoute escapeStrict inwardAvoid
  have escapeLast :
      ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
        gate).getLast? = some escapePoint := by
    rw [RetainedRay.rasterize_getLast?]
    rfl
  have shiftedTail :=
    shiftAvoid.join_left remainingAvoid
      (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
        escapePoint terminal.1 radialSlot)
      (RetainedRay.rasterize_head? _ _)
  have assembled :=
    sourceAvoid.join_left shiftedTail escapeLast
      (joinAtEndpoint_head?
        (retainedTerminalFanOuterLaneShiftRouteAt_head?
          escapePoint terminal.1 radialSlot))
  simpa [retainedTerminalFanOuterEscapedRadialRoute,
    gate, escapePoint, shiftedEscapePoint, localRoute] using assembled

/-- An escaped earlier radial route strictly avoids a later
order-compatible local route. -/
theorem
    retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_laterLocal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (secondDirection : RetainedTerminalDirection)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (directionsLe :
      terminal.1.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  apply
    retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_local_of_radial
      center terminal firstSlot secondSlot secondDirection
      lengthPositive escapeStrict
  exact
    retainedTerminalFanOuterRadialRoute_strictlyAvoid_laterLocal_of_positive
      center terminal firstSlot secondSlot secondDirection
      (by omega) directionsLe slotsLt

/-- An earlier local route strictly avoids a later order-compatible
escaped radial route. -/
theorem
    retainedTerminalFanOuterLocal_strictlyAvoid_laterEscapedRadialRoute
    (center : Cell)
    (firstDirection : RetainedTerminalDirection)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (directionsLe :
      firstDirection.angularRank ≤ terminal.1.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal secondSlot) := by
  exact
    (retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_local_of_radial
      center terminal secondSlot firstSlot firstDirection
      lengthPositive escapeStrict
      (retainedTerminalFanOuterLocal_strictlyAvoid_laterRadialRoute_of_positive
        center firstDirection terminal firstSlot secondSlot
        (by omega) directionsLe slotsLt).symm).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
