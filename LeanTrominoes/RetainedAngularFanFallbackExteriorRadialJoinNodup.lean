/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialNodup
import LeanTrominoes.RetainedAngularFanFallbackRadialSplitNormalization

/-! # Duplicate-free joins in the exterior fallback radial route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- Every subdivided lane-shift point lies no farther in the join
functional than the shifted gate where the radial ray begins. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_join_le_finish
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterLaneShiftRouteAt
          gate direction slot)) :
    Cell.linearValue
        (retainedFallbackRadialJoinNormal direction) point ≤
      Cell.linearValue
        (retainedFallbackRadialJoinNormal direction)
        (Cell.add gate
          (retainedTerminalFanOuterLaneOffset direction slot)) := by
  let route := retainedTerminalFanOuterLaneShiftRouteAt
    gate direction slot
  have routeHead : route.head? = some gate :=
    retainedTerminalFanOuterLaneShiftRouteAt_head?
      gate direction slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      gate direction slot
  apply
    AxisDirection.unitSubdividePolyline_linear_le_last_of_direction_nonnegative
      routeNonempty routeOrthogonal
      (retainedFallbackRadialJoinNormal direction)
      (finish := Cell.add gate
        (retainedTerminalFanOuterLaneOffset direction slot))
  · intro axis axisMember
    have directionsEq :
        Gadget.unitSubdivisionDirections route =
          prefixDirections .ordinary direction slot := by
      unfold route prefixDirections
      exact Gadget.unitSubdivisionDirections_translatePolyline gate _
    rw [directionsEq] at axisMember
    exact ordinaryPrefixDirections_join_nonnegative
      direction slot axis axisMember
  · exact retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      gate direction slot
  · exact pointMember

/-- After the head of a positive inward ray, every subdivided point lies
strictly beyond its start in the join functional. -/
theorem retainedTerminalFanOuterInwardRayOfLength_tail_join_gt_start
    (direction : RetainedTerminalDirection)
    (count : Nat)
    (start point : Cell)
    (positive : 0 < count)
    (pointMember :
      point ∈
        (AxisDirection.unitSubdividePolyline
          ((retainedTerminalFanOuterInwardRayOfLength
            direction count).rasterize start)).tail) :
    Cell.linearValue
        (retainedFallbackRadialJoinNormal direction) start <
      Cell.linearValue
        (retainedFallbackRadialJoinNormal direction) point := by
  let route :=
    (retainedTerminalFanOuterInwardRayOfLength
      direction count).rasterize start
  have routeHead : route.head? = some start :=
    RetainedRay.rasterize_head? _ _
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    RetainedRay.rasterize_orthogonal _ _
  apply AxisDirection.unitSubdividePolyline_tail_linear_gt_head
    routeNonempty routeOrthogonal
    (retainedFallbackRadialJoinNormal direction)
    routeHead
  · intro axis axisMember
    have directionsEq :
        Gadget.unitSubdivisionDirections route =
          radialCopies count direction :=
      retainedTerminalFanOuterInwardRayOfLength_directions
        direction count start
    rw [directionsEq] at axisMember
    exact radialCopies_join_nonnegative
      count direction axis axisMember
  · intro axis axisHead
    have directionsEq :
        Gadget.unitSubdivisionDirections route =
          radialCopies count direction :=
      retainedTerminalFanOuterInwardRayOfLength_directions
        direction count start
    rw [directionsEq] at axisHead
    exact radialCopies_join_head_positive
      count direction positive axis axisHead
  · exact pointMember

/-- The shortened inward ray is the common explicitly-length-indexed ray. -/
theorem retainedTerminalFanOuterInwardPrefixRay_eq_ofLength
    (terminal : RetainedTerminalData) :
    retainedTerminalFanOuterInwardPrefixRay terminal =
      retainedTerminalFanOuterInwardRayOfLength terminal.1
        (retainedTerminalFanOuterRadialLength terminal - 1) := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

/-- The whole exterior radial prefix has duplicate-free unit subdivision,
including the zero-length shortened-ray case. -/
theorem retainedTerminalFanOuterRadialPrefix_unitSubdivide_nodup
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (AxisDirection.unitSubdividePolyline
      (retainedTerminalFanOuterRadialPrefix
        center terminal slot)).Nodup := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let shiftRoute := retainedTerminalFanOuterLaneShiftRouteAt
    gate terminal.1 slot
  let rayRoute :=
    (retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
      shiftedGate
  have prefixEq :
      retainedTerminalFanOuterRadialPrefix center terminal slot =
        joinAtEndpoint shiftRoute rayRoute := by
    rfl
  have shiftHead : shiftRoute.head? = some gate :=
    retainedTerminalFanOuterLaneShiftRouteAt_head?
      gate terminal.1 slot
  have shiftNonempty : shiftRoute ≠ [] := by
    intro empty
    rw [empty] at shiftHead
    simp at shiftHead
  have shiftLast : shiftRoute.getLast? = some shiftedGate :=
    retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      gate terminal.1 slot
  have rayHead : rayRoute.head? = some shiftedGate :=
    RetainedRay.rasterize_head? _ _
  have shiftNodup :
      (AxisDirection.unitSubdividePolyline shiftRoute).Nodup :=
    retainedTerminalFanOuterLaneShiftRouteAt_unitSubdivide_nodup
      gate terminal.1 slot
  have rayNodup :
      (AxisDirection.unitSubdividePolyline rayRoute).Nodup := by
    unfold rayRoute
    rw [retainedTerminalFanOuterInwardPrefixRay_eq_ofLength]
    exact
      retainedTerminalFanOuterInwardRayOfLength_unitSubdivide_nodup
        terminal.1
        (retainedTerminalFanOuterRadialLength terminal - 1)
        shiftedGate
  rw [prefixEq,
    AxisDirection.unitSubdividePolyline_joinAtEndpoint
      shiftNonempty shiftLast rayHead,
    joinAtEndpoint]
  apply shiftNodup.append rayNodup.tail
  rw [List.disjoint_left]
  intro point shiftMember rayTailMember
  by_cases countZero :
      retainedTerminalFanOuterRadialLength terminal - 1 = 0
  · unfold rayRoute at rayTailMember
    rw [retainedTerminalFanOuterInwardPrefixRay_eq_ofLength,
      countZero] at rayTailMember
    rcases terminal with ⟨direction, length⟩
    cases direction <;>
      simp [retainedTerminalFanOuterInwardRayOfLength,
        RetainedRay.rasterize, compassRay,
        routedClauseRay] at rayTailMember
  · have countPositive :
        0 < retainedTerminalFanOuterRadialLength terminal - 1 :=
      Nat.pos_of_ne_zero countZero
    have shiftUpper :=
      retainedTerminalFanOuterLaneShiftRouteAt_join_le_finish
        gate terminal.1 slot point shiftMember
    have rayLower :
        Cell.linearValue
            (retainedFallbackRadialJoinNormal terminal.1)
            shiftedGate <
          Cell.linearValue
            (retainedFallbackRadialJoinNormal terminal.1)
            point := by
      unfold rayRoute at rayTailMember
      rw [retainedTerminalFanOuterInwardPrefixRay_eq_ofLength]
        at rayTailMember
      exact
        retainedTerminalFanOuterInwardRayOfLength_tail_join_gt_start
          terminal.1
          (retainedTerminalFanOuterRadialLength terminal - 1)
          shiftedGate point countPositive rayTailMember
    exact (not_lt_of_ge shiftUpper rayLower)

/-- Every exterior prefix point lies no farther in the join functional than
its one-primitive-outside endpoint. -/
theorem retainedTerminalFanOuterRadialPrefix_join_le_finish
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialPrefix
          center terminal slot)) :
    Cell.linearValue
        (retainedFallbackRadialJoinNormal terminal.1) point ≤
      Cell.linearValue
        (retainedFallbackRadialJoinNormal terminal.1)
        (Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
            terminal.1.primitive)) := by
  let route := retainedTerminalFanOuterRadialPrefix
    center terminal slot
  have routeHead :
      route.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterRadialPrefix_head?
      center terminal slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterRadialPrefix_orthogonal
      center terminal slot
  apply
    AxisDirection.unitSubdividePolyline_linear_le_last_of_direction_nonnegative
      routeNonempty routeOrthogonal
      (retainedFallbackRadialJoinNormal terminal.1)
      (finish := Cell.add center
        (Cell.add
          (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
          terminal.1.primitive))
  · intro axis axisMember
    have directionsEq :=
      retainedTerminalFanOuterRadialPrefix_directions
        center terminal slot
    change Gadget.unitSubdivisionDirections route = _ at directionsEq
    rw [directionsEq, List.mem_append] at axisMember
    rcases axisMember with prefixMember | radialMember
    · exact ordinaryPrefixDirections_join_nonnegative
        terminal.1 slot axis prefixMember
    · exact radialCopies_join_nonnegative
        (retainedTerminalFanOuterRadialLength terminal - 1)
        terminal.1 axis radialMember
  · exact retainedTerminalFanOuterRadialPrefix_getLast?
      center terminal slot radialPositive
  · exact pointMember

/-- The positioned final primitive block has duplicate-free ordered unit
subdivision. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_unitSubdivide_nodup
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (AxisDirection.unitSubdividePolyline
      (retainedTerminalFanOuterRadialFinalStubAt
        center direction slot)).Nodup := by
  let route := retainedTerminalFanOuterRadialFinalStubAt
    center direction slot
  have routeHead :
      route.head? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset direction slot)
              direction.primitive)) :=
    retainedTerminalFanOuterRadialFinalStubAt_head?
      center direction slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterRadialFinalStubAt_orthogonal
      center direction slot
  apply
    AxisDirection.unitSubdividePolyline_nodup_of_direction_linear_negative
      routeNonempty routeOrthogonal
      (retainedFallbackRadialProgressNormal direction)
  intro axis axisMember
  have directionsEq :=
    retainedTerminalFanOuterRadialFinalStubAt_directions
      center direction slot
  change Gadget.unitSubdivisionDirections route = _ at directionsEq
  rw [directionsEq] at axisMember
  exact inwardRayUnitDirections_progress_negative
    direction axis axisMember

/-- Every subdivided point after the head of the final primitive lies
strictly beyond that head in the join functional. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_tail_join_gt_head
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈
        (AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterRadialFinalStubAt
            center direction slot)).tail) :
    Cell.linearValue
        (retainedFallbackRadialJoinNormal direction)
        (Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset direction slot)
            direction.primitive)) <
      Cell.linearValue
        (retainedFallbackRadialJoinNormal direction) point := by
  let route := retainedTerminalFanOuterRadialFinalStubAt
    center direction slot
  have routeHead :
      route.head? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset direction slot)
              direction.primitive)) :=
    retainedTerminalFanOuterRadialFinalStubAt_head?
      center direction slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterRadialFinalStubAt_orthogonal
      center direction slot
  apply AxisDirection.unitSubdividePolyline_tail_linear_gt_head
    routeNonempty routeOrthogonal
    (retainedFallbackRadialJoinNormal direction)
    routeHead
  · intro axis axisMember
    have directionsEq :=
      retainedTerminalFanOuterRadialFinalStubAt_directions
        center direction slot
    change Gadget.unitSubdivisionDirections route = _ at directionsEq
    rw [directionsEq] at axisMember
    exact inwardRayUnitDirections_join_nonnegative
      direction axis axisMember
  · intro axis axisHead
    have directionsEq :=
      retainedTerminalFanOuterRadialFinalStubAt_directions
        center direction slot
    change Gadget.unitSubdivisionDirections route = _ at directionsEq
    rw [directionsEq] at axisHead
    exact inwardRayUnitDirections_join_head_positive
      direction axis axisHead
  · exact pointMember

/-- Splitting the last primitive from a positive radial route preserves a
duplicate-free complete unit path. -/
theorem splitRadialRoute_unitSubdivide_nodup
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    (AxisDirection.unitSubdividePolyline
      (splitRadialRoute center terminal slot)).Nodup := by
  let radialPrefix := retainedTerminalFanOuterRadialPrefix
    center terminal slot
  let stub := retainedTerminalFanOuterRadialFinalStubAt
    center terminal.1 slot
  let boundary := Cell.add center
    (Cell.add
      (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
      terminal.1.primitive)
  have prefixHead :
      radialPrefix.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterRadialPrefix_head?
      center terminal slot
  have prefixNonempty : radialPrefix ≠ [] := by
    intro empty
    rw [empty] at prefixHead
    simp at prefixHead
  have stubHead : stub.head? = some boundary :=
    retainedTerminalFanOuterRadialFinalStubAt_head?
      center terminal.1 slot
  have prefixLast : radialPrefix.getLast? = some boundary :=
    retainedTerminalFanOuterRadialPrefix_getLast?
      center terminal slot radialPositive
  have prefixNodup :
      (AxisDirection.unitSubdividePolyline radialPrefix).Nodup :=
    retainedTerminalFanOuterRadialPrefix_unitSubdivide_nodup
      center terminal slot
  have stubNodup :
      (AxisDirection.unitSubdividePolyline stub).Nodup :=
    retainedTerminalFanOuterRadialFinalStubAt_unitSubdivide_nodup
      center terminal.1 slot
  unfold splitRadialRoute
  rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
    prefixNonempty prefixLast stubHead,
    joinAtEndpoint]
  apply prefixNodup.append stubNodup.tail
  rw [List.disjoint_left]
  intro point prefixMember stubTailMember
  have prefixUpper :=
    retainedTerminalFanOuterRadialPrefix_join_le_finish
      center terminal slot radialPositive point prefixMember
  have stubLower :=
    retainedTerminalFanOuterRadialFinalStubAt_tail_join_gt_head
      center terminal.1 slot point stubTailMember
  exact (not_lt_of_ge prefixUpper stubLower)

/-- Consequently, the exterior prefix and final primitive meet only at
their advertised subdivided boundary. -/
theorem retainedTerminalFanOuterRadialPrefix_finalStub_only_common
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    ∀ point,
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialPrefix center terminal slot) →
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialFinalStubAt
          center terminal.1 slot) →
      point =
        Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
            terminal.1.primitive) := by
  let radialPrefix := retainedTerminalFanOuterRadialPrefix
    center terminal slot
  let stub := retainedTerminalFanOuterRadialFinalStubAt
    center terminal.1 slot
  let boundary := Cell.add center
    (Cell.add
      (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
      terminal.1.primitive)
  have prefixHead :
      radialPrefix.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    retainedTerminalFanOuterRadialPrefix_head?
      center terminal slot
  have prefixNonempty : radialPrefix ≠ [] := by
    intro empty
    rw [empty] at prefixHead
    simp at prefixHead
  have stubHead : stub.head? = some boundary :=
    retainedTerminalFanOuterRadialFinalStubAt_head?
      center terminal.1 slot
  have stubNonempty : stub ≠ [] := by
    intro empty
    rw [empty] at stubHead
    simp at stubHead
  have prefixLast : radialPrefix.getLast? = some boundary :=
    retainedTerminalFanOuterRadialPrefix_getLast?
      center terminal slot radialPositive
  exact
    AxisDirection.unitSubdividePolyline_only_common_of_join_nodup
      prefixNonempty stubNonempty prefixLast stubHead
      (splitRadialRoute_unitSubdivide_nodup
        center terminal slot radialPositive)

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
