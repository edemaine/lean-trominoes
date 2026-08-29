/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackEscapedRadialPrefixEndpoint
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedCrossSeparation

/-! # Separation of escaped fallback radial prefixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every listed point of an escaped exterior prefix lies strictly outside
the radius-288 supporting side. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_side_lower
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterEscapedRadialPrefix
        center terminal slot) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1)
        point := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedPoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  rw [retainedTerminalFanOuterEscapedRadialPrefix] at pointMember
  change point ∈
    joinAtEndpoint
      ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate)
      (joinAtEndpoint
        (retainedTerminalFanOuterLaneShiftRouteAt
          escapePoint terminal.1 slot)
        ((retainedTerminalFanOuterEscapedRemainingPrefixRay terminal).rasterize
          shiftedPoint)) at pointMember
  rcases mem_joinAtEndpoint pointMember with sourceMember | shiftedMember
  · exact retainedTerminalFanOuterSourceEscapeRay_side_strict_lower
      center terminal slot lengthPositive escapeStrict point sourceMember
  · rcases mem_joinAtEndpoint shiftedMember with
      laneMember | remainingMember
    · exact retainedTerminalFanOuterDelayedLaneShift_side_strict_lower
        center terminal slot lengthPositive escapeStrict point laneMember
    · have outward :=
        retainedTerminalFanOuterInwardRayOfLength_side_ge_finish
          terminal.1
          (retainedTerminalFanOuterRadialLength terminal -
            retainedTerminalFanOuterSourceEscapeLength - 1)
          shiftedPoint point
          (by simpa [retainedTerminalFanOuterEscapedRemainingPrefixRay]
            using remainingMember)
      have remainingLast :=
        retainedTerminalFanOuterEscapedRemainingPrefix_getLast?
          center terminal slot escapeStrict
      rw [RetainedRay.rasterize_getLast?] at remainingLast
      have finishEq := Option.some.inj remainingLast
      change
        Cell.linearValue
            (retainedTerminalFanOuterSideNormal terminal.1)
            (Cell.add shiftedPoint
              (retainedTerminalFanOuterEscapedRemainingPrefixRay
                terminal).vector) ≤
          Cell.linearValue
            (retainedTerminalFanOuterSideNormal terminal.1) point
        at outward
      rw [finishEq, Cell.linearValue_add, Cell.linearValue_add,
        retainedTerminalFanOuterSideNormal_lanePortOffset] at outward
      have primitivePositive :=
        retainedTerminalFanOuterSideNormal_primitive_positive terminal.1
      omega

/-- An escaped exterior prefix is continuously separated from every local
fan adapter. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_strictlyAvoid_local
    (center : Cell)
    (terminal : RetainedTerminalData)
    (radialSlot localSlot : RetainedTerminalSlot)
    (localDirection : RetainedTerminalDirection)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialPrefix
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
      (retainedTerminalFanOuterEscapedRadialPrefix_side_lower
        center terminal radialSlot lengthPositive escapeStrict)).symm

/-- An escaped exterior prefix is continuously separated from every
Figure 7 spoke at its fan center. -/
theorem
    retainedTerminalFanOuterEscapedRadialPrefix_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialPrefix
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 96)
      (fun point pointMember => by
        rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
          at pointMember
        rcases List.mem_map.mp pointMember with
          ⟨offset, offsetMember, rfl⟩
        have upper :=
          retainedTerminalFanCenteredFigure7Spoke_side_upper
            terminal.1 secondSlot offset offsetMember
        rw [Cell.linearValue_add]
        omega)
      (fun point pointMember => by
        have lower :=
          retainedTerminalFanOuterEscapedRadialPrefix_side_lower
            center terminal firstSlot lengthPositive escapeStrict
            point pointMember
        omega)).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
