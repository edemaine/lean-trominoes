/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedNormalizedFirstDirections

/-! # Source-head isolation after appending a Figure 7 spoke -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

private theorem
    retainedTerminalFanFigure7SpokeRouteAt_cardinal_linear_upper
    (center : Cell)
    (port : Port)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanFigure7SpokeRouteAt center slot) :
    Cell.linearValue port.unitVector point ≤
      Cell.linearValue port.unitVector center + 96 := by
  rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨offset, offsetMember, rfl⟩
  have bounded :=
    retainedTerminalFanCenteredFigure7Spoke_side_upper
      (.compass port) slot offset offsetMember
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simpa [retainedTerminalFanOuterSideNormal,
      Port.unitVector, Cell.linearValue, Cell.add] using bounded

private theorem
    retainedTerminalFanFigure7SpokeRouteAt_unit_cardinal_linear_upper
    (center : Cell)
    (port : Port)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanFigure7SpokeRouteAt center slot)) :
    Cell.linearValue port.unitVector point ≤
      Cell.linearValue port.unitVector center + 96 := by
  have orthogonal :=
    retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        orthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact
      retainedTerminalFanFigure7SpokeRouteAt_cardinal_linear_upper
        center port slot cardinal point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    apply Cell.linearValue_le_of_segment_contains port.unitVector
      (Cell.linearValue port.unitVector center + 96)
    · exact
        retainedTerminalFanFigure7SpokeRouteAt_cardinal_linear_upper
          center port slot cardinal segment.start endpoints.1
    · exact
        retainedTerminalFanFigure7SpokeRouteAt_cardinal_linear_upper
          center port slot cardinal segment.finish endpoints.2
    · exact GridSegment.contains_of_interiorContains interior

private theorem
    retainedTerminalFanOuterDemand_gate_cardinal_linear_lower
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    Cell.linearValue port.unitVector center + 96 <
      Cell.linearValue port.unitVector
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  rcases center with ⟨centerX, centerY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive,
      Port.unitVector, Cell.linearValue, Cell.add, Cell.scale] <;>
    omega

/-- The source gate of a cardinal escaped fan is absent from the entire
unit-subdivided Figure 7 spoke appended at that fan's boundary. -/
theorem retainedTerminalFanOuterEscaped_gate_not_mem_unitFigure7Spoke
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    (retainedAngularFanOuterDemand
        center (.compass port, length) slot).gate ∉
      AxisDirection.unitSubdividePolyline
        (retainedTerminalFanFigure7SpokeRouteAt center slot) := by
  intro member
  have upper :=
    retainedTerminalFanFigure7SpokeRouteAt_unit_cardinal_linear_upper
      center port slot cardinal _ member
  have lower :=
    retainedTerminalFanOuterDemand_gate_cardinal_linear_lower
      center port length slot cardinal lengthLarge
  omega

/-- Appending the matching Figure 7 spoke to a cardinal escaped outer fan
does not introduce a second visit to the source gate. -/
theorem
    retainedTerminalFanOuterEscapedCompleteFigure7Route_headNotInTail
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterEscapedCompleteRoute
            center (.compass port, length) slot)
          (retainedTerminalFanFigure7SpokeRouteAt center slot))) := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let outer :=
    retainedTerminalFanOuterEscapedCompleteRoute center terminal slot
  let spoke := retainedTerminalFanFigure7SpokeRouteAt center slot
  let gate := (retainedAngularFanOuterDemand center terminal slot).gate
  have lengthPositive : 0 < length := by omega
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simp [terminal, retainedTerminalFanOuterSourceEscapeLength,
      retainedTerminalFanOuterRadialLength,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalInterfaceMultiplier]
    omega
  apply
    (retainedTerminalFanOuterEscapedCompleteRoute_headNotInTail
      center port length slot cardinal lengthLarge)
      |>.unitSubdividePolyline_joinAtEndpoint
  · intro outerEmpty
    have head :=
      retainedTerminalFanOuterEscapedCompleteRoute_head?
        center terminal slot
    rw [outerEmpty] at head
    simp at head
  · exact retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  · exact retainedTerminalFanOuterEscapedCompleteRoute_getLast?
      center terminal slot lengthPositive escapeFits
  · exact retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  · exact
      retainedTerminalFanOuterEscaped_gate_not_mem_unitFigure7Spoke
        center port length slot cardinal lengthLarge

end PeriodicEightOccurrenceSplit
end LeanTrominoes
