/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineStrictDirectionNodup
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialDirectionSemantics

/-! # Duplicate-free exterior fallback radial routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- A finite direction-dependent functional strictly traversed by every
unit step of one inward retained-ray primitive. -/
def retainedFallbackRadialProgressNormal
    (direction : RetainedTerminalDirection) : Cell :=
  Cell.scale (-1 : Int)
    ((inwardRayUnitDirections direction).foldl
      (fun total axis => Cell.add total axis.step) (0, 0))

/-- The negative progress functional strictly decreases on every unit step
used by an inward retained-ray primitive. -/
theorem inwardRayUnitDirections_progress_negative :
    ∀ (direction : RetainedTerminalDirection)
      (axis : AxisDirection),
      axis ∈ inwardRayUnitDirections direction →
        Cell.linearValue
            (retainedFallbackRadialProgressNormal direction)
            axis.step < 0 := by
  native_decide

/-- Repeating an inward primitive preserves strict progress. -/
theorem radialCopies_progress_negative
    (count : Nat)
    (direction : RetainedTerminalDirection)
    (axis : AxisDirection)
    (member : axis ∈ radialCopies count direction) :
    Cell.linearValue
        (retainedFallbackRadialProgressNormal direction)
        axis.step < 0 := by
  rw [radialCopies] at member
  rcases List.mem_flatten.mp member with
    ⟨block, blockMember, axisMember⟩
  have blockEq : block = inwardRayUnitDirections direction :=
    List.eq_of_mem_replicate blockMember
  subst block
  exact inwardRayUnitDirections_progress_negative
    direction axis axisMember

/-- A finite functional oriented along the first unit step of the inward
ray.  Lane-shift points lie no farther than their endpoint in this
functional, while every later radial point lies strictly beyond it. -/
def retainedFallbackRadialJoinNormal
    (direction : RetainedTerminalDirection) : Cell :=
  match (inwardRayUnitDirections direction).head? with
  | some axis => axis.step
  | none => (0, 0)

theorem inwardRayUnitDirections_ne_nil :
    ∀ direction : RetainedTerminalDirection,
      inwardRayUnitDirections direction ≠ [] := by
  native_decide

theorem inwardRayUnitDirections_join_nonnegative :
    ∀ (direction : RetainedTerminalDirection)
      (axis : AxisDirection),
      axis ∈ inwardRayUnitDirections direction →
        0 ≤
          Cell.linearValue
            (retainedFallbackRadialJoinNormal direction)
            axis.step := by
  native_decide

theorem inwardRayUnitDirections_join_head_positive :
    ∀ (direction : RetainedTerminalDirection)
      (axis : AxisDirection),
      (inwardRayUnitDirections direction).head? = some axis →
        0 <
          Cell.linearValue
            (retainedFallbackRadialJoinNormal direction)
            axis.step := by
  native_decide

theorem radialCopies_join_nonnegative
    (count : Nat)
    (direction : RetainedTerminalDirection)
    (axis : AxisDirection)
    (member : axis ∈ radialCopies count direction) :
    0 ≤
      Cell.linearValue
        (retainedFallbackRadialJoinNormal direction)
        axis.step := by
  rw [radialCopies] at member
  rcases List.mem_flatten.mp member with
    ⟨block, blockMember, axisMember⟩
  have blockEq : block = inwardRayUnitDirections direction :=
    List.eq_of_mem_replicate blockMember
  subst block
  exact inwardRayUnitDirections_join_nonnegative
    direction axis axisMember

theorem radialCopies_join_head_positive
    (count : Nat)
    (direction : RetainedTerminalDirection)
    (positive : 0 < count)
    (axis : AxisDirection)
    (head : (radialCopies count direction).head? = some axis) :
    0 <
      Cell.linearValue
        (retainedFallbackRadialJoinNormal direction)
        axis.step := by
  cases count with
  | zero => omega
  | succ count =>
      have primitiveNonempty :=
        inwardRayUnitDirections_ne_nil direction
      rw [radialCopies, List.replicate_succ,
        List.flatten_cons,
        List.head?_append_of_ne_nil _ primitiveNonempty] at head
      exact inwardRayUnitDirections_join_head_positive
        direction axis head

/-- A direction chosen from the one-segment lane shift makes every present
lane-shift unit direction strictly decreasing. -/
def retainedFallbackLaneProgressNormal
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : Cell :=
  match (prefixDirections .ordinary direction slot).head? with
  | some axis => Cell.scale (-1 : Int) axis.step
  | none => (0, 0)

theorem ordinaryPrefixDirections_lane_progress_negative :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot)
      (axis : AxisDirection),
      axis ∈ prefixDirections .ordinary direction slot →
        Cell.linearValue
            (retainedFallbackLaneProgressNormal direction slot)
            axis.step < 0 := by
  native_decide

theorem ordinaryPrefixDirections_join_nonnegative :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot)
      (axis : AxisDirection),
      axis ∈ prefixDirections .ordinary direction slot →
        0 ≤
          Cell.linearValue
            (retainedFallbackRadialJoinNormal direction)
            axis.step := by
  native_decide

/-- Any number of repeated inward primitive blocks has duplicate-free
ordered unit subdivision. -/
theorem retainedTerminalFanOuterInwardRayOfLength_unitSubdivide_nodup
    (direction : RetainedTerminalDirection)
    (count : Nat)
    (start : Cell) :
    (AxisDirection.unitSubdividePolyline
      ((retainedTerminalFanOuterInwardRayOfLength
        direction count).rasterize start)).Nodup := by
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
  apply
    AxisDirection.unitSubdividePolyline_nodup_of_direction_linear_negative
      routeNonempty routeOrthogonal
      (retainedFallbackRadialProgressNormal direction)
  intro axis axisMember
  have directionsEq :
      Gadget.unitSubdivisionDirections route =
        radialCopies count direction := by
    exact retainedTerminalFanOuterInwardRayOfLength_directions
      direction count start
  rw [directionsEq] at axisMember
  exact radialCopies_progress_negative
    count direction axis axisMember

/-- Every positioned finite lane shift has duplicate-free ordered unit
subdivision. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_unitSubdivide_nodup
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (AxisDirection.unitSubdividePolyline
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate direction slot)).Nodup := by
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
    AxisDirection.unitSubdividePolyline_nodup_of_direction_linear_negative
      routeNonempty routeOrthogonal
      (retainedFallbackLaneProgressNormal direction slot)
  intro axis axisMember
  have directionsEq :
      Gadget.unitSubdivisionDirections route =
        prefixDirections .ordinary direction slot := by
    unfold route prefixDirections
    exact Gadget.unitSubdivisionDirections_translatePolyline gate _
  rw [directionsEq] at axisMember
  exact ordinaryPrefixDirections_lane_progress_negative
    direction slot axis axisMember

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
