/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateTangentData
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-! # Cardinal gate-tangent/radial contact localization -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

private theorem negativeLinearValue_le_of_le
    (normal gate point : Cell)
    (lower : Cell.linearValue normal gate ≤
      Cell.linearValue normal point) :
    Cell.linearValue (Cell.scale (-1) normal) point ≤
      -Cell.linearValue normal gate := by
  rcases normal with ⟨normalX, normalY⟩
  rcases gate with ⟨gateX, gateY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.linearValue, Cell.scale] at lower ⊢
  omega

private theorem linearValue_le_of_negativeLinearValue_le
    (normal gate point : Cell)
    (upper : Cell.linearValue (Cell.scale (-1) normal) point ≤
      -Cell.linearValue normal gate) :
    Cell.linearValue normal gate ≤
      Cell.linearValue normal point := by
  rcases normal with ⟨normalX, normalY⟩
  rcases gate with ⟨gateX, gateY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.linearValue, Cell.scale] at upper ⊢
  omega

/-- Every unit-subdivision point of a positive backward tangent other than
its gate lies strictly behind that gate in the tangential coordinate. -/
theorem retainedTerminalFanCardinalBackwardTangentRoute_unit_side_lt_of_ne_gate
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (distancePositive : 0 < distance)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalBackwardTangentRoute
          center port length slot distance))
    (pointNe :
      point ≠
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate) :
    Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port)) point <
      Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  let start := Cell.add gate
    (Cell.scale (-(distance : Int))
      (retainedTerminalFanOuterLaneStep (.compass port)))
  change point ∈ AxisDirection.unitSubdividePolyline [start, gate]
    at pointMember
  change point ≠ gate at pointNe
  simp only [AxisDirection.unitSubdividePolyline,
    joinAtEndpoint, List.tail_cons, List.append_nil] at pointMember
  unfold AxisDirection.unitSegmentPoints at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨index, indexMember, rfl⟩
  have indexLt :
      index < AxisDirection.segmentLength start gate + 1 :=
    List.mem_range.mp indexMember
  change Cell.linearValue
      (retainedTerminalFanOuterLaneStep (.compass port))
      (Cell.add start
        (Cell.scale (index : Int)
          (AxisDirection.between start gate).step)) <
    Cell.linearValue
      (retainedTerminalFanOuterLaneStep (.compass port)) gate
  have distanceNe : distance ≠ 0 := Nat.ne_of_gt distancePositive
  have distanceCastNonnegative : (0 : Int) ≤ distance := by
    exact_mod_cast Nat.zero_le distance
  have distanceCastNotNegative : ¬ (distance : Int) < 0 :=
    not_lt_of_ge distanceCastNonnegative
  rcases gate with ⟨gateX, gateY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [start, retainedTerminalFanOuterLaneStep,
      AxisDirection.segmentLength, AxisDirection.between,
      AxisDirection.step, Cell.linearValue, Cell.add, Cell.scale,
      distancePositive, distanceNe, distanceCastNotNegative]
      at indexLt pointNe ⊢ <;>
    omega

/-- Every listed point of a cardinal ordinary radial route lies on or ahead
of its source gate in the clockwise tangential coordinate. -/
theorem retainedTerminalFanOuterRadialRoute_cardinal_tangent_lower
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
      point ∈ retainedTerminalFanOuterRadialRoute
        center (.compass port, length) slot) :
    Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate ≤
      Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port)) point := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate := (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  change point ∈
    joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate terminal.1 slot)
      ((retainedTerminalFanOuterInwardRay terminal).rasterize
        shiftedGate) at pointMember
  rcases mem_joinAtEndpoint pointMember with shiftMember | rayMember
  · unfold retainedTerminalFanOuterLaneShiftRouteAt
      PeriodicOrthocrossing.translatePolyline at shiftMember
    rw [List.mem_map] at shiftMember
    rcases shiftMember with ⟨offset, offsetMember, rfl⟩
    by_cases slotZero : slot.val = 0
    · simp [retainedTerminalFanOuterLaneShiftRoute,
        slotZero] at offsetMember
      subst offset
      simp [terminal, gate, Cell.linearValue, Cell.add]
    · simp [retainedTerminalFanOuterLaneShiftRoute,
        slotZero] at offsetMember
      rcases offsetMember with rfl | rfl
      · simp [terminal, gate, Cell.linearValue, Cell.add]
      · rcases cardinal with rfl | rfl | rfl | rfl <;>
          simp [terminal, gate,
            retainedTerminalFanOuterLaneOffset,
            retainedTerminalFanOuterLaneStep,
            retainedTerminalFanOuterLaneSpacing,
            Cell.linearValue, Cell.add, Cell.scale]
  · have radialPositive :
        0 < retainedTerminalFanOuterRadialLength terminal := by
      simp [terminal, retainedTerminalFanOuterRadialLength,
        retainedTerminalFanTotalRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalInterfaceMultiplier]
      omega
    have oppositeCardinal :
        oppositePort port = .north ∨ oppositePort port = .east ∨
          oppositePort port = .south ∨ oppositePort port = .west := by
      rcases cardinal with rfl | rfl | rfl | rfl <;>
        simp [oppositePort]
    change point ∈ compassRay (oppositePort port)
      (retainedTerminalFanOuterRadialLength terminal) shiftedGate
      at rayMember
    rw [compassRay_eq_pair_of_cardinal
      (oppositePort port)
      (retainedTerminalFanOuterRadialLength terminal)
      radialPositive shiftedGate oppositeCardinal] at rayMember
    have shiftedLower :
        Cell.linearValue
            (retainedTerminalFanOuterLaneStep terminal.1) gate ≤
          Cell.linearValue
            (retainedTerminalFanOuterLaneStep terminal.1) shiftedGate := by
      rcases cardinal with rfl | rfl | rfl | rfl <;>
        simp [terminal, gate, shiftedGate,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          Cell.linearValue, Cell.add, Cell.scale]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rayMember
    rcases rayMember with rfl | rfl
    · exact shiftedLower
    · have perpendicular :
          Cell.linearValue
              (retainedTerminalFanOuterLaneStep terminal.1)
              (oppositePort port).unitVector = 0 := by
        rcases cardinal with rfl | rfl | rfl | rfl <;>
          simp [terminal, retainedTerminalFanOuterLaneStep,
            oppositePort, Port.unitVector, Cell.linearValue]
      rw [Cell.linearValue_add, Cell.linearValue_scale,
        perpendicular, mul_zero, add_zero]
      exact shiftedLower

/-- The same weak tangential lower bound holds at every lattice point
introduced by unit subdivision of the cardinal radial route. -/
theorem retainedTerminalFanOuterRadialRoute_unit_cardinal_tangent_lower
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
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialRoute
          center (.compass port, length) slot)) :
    Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate ≤
      Cell.linearValue
        (retainedTerminalFanOuterLaneStep (.compass port)) point := by
  let radial := retainedTerminalFanOuterRadialRoute
    center (.compass port, length) slot
  let normal := retainedTerminalFanOuterLaneStep (.compass port)
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  have radialOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline radial :=
    retainedTerminalFanOuterRadialRoute_orthogonal
      center (.compass port, length) slot
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        radialOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact retainedTerminalFanOuterRadialRoute_cardinal_tangent_lower
      center port length slot cardinal lengthLarge point originalMember
  · have endpoints := gridPolylineSegments_endpoints_mem segmentMember
    have startLower :=
      retainedTerminalFanOuterRadialRoute_cardinal_tangent_lower
        center port length slot cardinal lengthLarge
        segment.start endpoints.1
    have finishLower :=
      retainedTerminalFanOuterRadialRoute_cardinal_tangent_lower
        center port length slot cardinal lengthLarge
        segment.finish endpoints.2
    change Cell.linearValue normal gate ≤
      Cell.linearValue normal segment.start at startLower
    change Cell.linearValue normal gate ≤
      Cell.linearValue normal segment.finish at finishLower
    have negativeUpper := Cell.linearValue_le_of_segment_contains
      (Cell.scale (-1) normal)
      (-Cell.linearValue normal gate)
      (segment := segment) (point := point)
      (negativeLinearValue_le_of_le
        normal gate segment.start startLower)
      (negativeLinearValue_le_of_le
        normal gate segment.finish finishLower)
      (GridSegment.contains_of_interiorContains interior)
    exact linearValue_le_of_negativeLinearValue_le
      normal gate point negativeUpper

/-- A positive cardinal source tangent and its ordinary radial lane meet
after unit subdivision only at their common gate. -/
theorem retainedTerminalFanCardinalBackwardTangentRoute_only_common_radial
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (distancePositive : 0 < distance) :
    ∀ point,
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalBackwardTangentRoute
          center port length slot distance) →
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialRoute
          center (.compass port, length) slot) →
      point =
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  intro point tangentMember radialMember
  by_contra pointNe
  have tangentLt :=
    retainedTerminalFanCardinalBackwardTangentRoute_unit_side_lt_of_ne_gate
      center port length slot distance cardinal distancePositive
      point tangentMember pointNe
  have radialLower :=
    retainedTerminalFanOuterRadialRoute_unit_cardinal_tangent_lower
      center port length slot cardinal lengthLarge point radialMember
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
