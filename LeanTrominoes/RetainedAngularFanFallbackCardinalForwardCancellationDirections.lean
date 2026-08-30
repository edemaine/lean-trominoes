/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationPolyline
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardNormalizedDirections

/-! # Direction words at a forward-cardinal cancellation junction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Direction from a forward tangential predecessor toward a cardinal fan
gate.  Noncardinal ports are irrelevant total cases. -/
def retainedTerminalFanCardinalForwardDirection : Port → AxisDirection
  | .east => .south
  | .south => .east
  | .west => .north
  | .north => .west
  | _ => .invalid

theorem retainedTerminalFanCardinalForwardDirection_genuine
    (port : Port)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    (retainedTerminalFanCardinalForwardDirection port).IsGenuine := by
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    decide

/-- The unit overlap traverses one constant forward-tangent direction for
exactly one lane displacement. -/
theorem retainedTerminalFanCardinalForwardOverlapPath_directions
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanCardinalForwardOverlapPath
          center port length slot) =
      List.replicate
        (retainedTerminalFanOuterLaneSpacing * slot.val)
        (retainedTerminalFanCardinalForwardDirection port) := by
  let overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot
  have overlapOrthogonal : OrthogonalPolyline overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
      center port length slot
  unfold retainedTerminalFanCardinalForwardOverlapPath
  rw [Gadget.unitSubdivisionDirections_unitSubdividePolyline
    overlapRoute overlapOrthogonal]
  rcases center with ⟨centerX, centerY⟩
  by_cases slotZero : slot.val = 0 <;>
    rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [overlapRoute,
      retainedTerminalFanCardinalForwardTangentOverlapRoute,
      retainedTerminalFanOuterLaneShiftRouteAt,
      retainedTerminalFanOuterLaneShiftRoute,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanCardinalForwardDirection,
      retainedTerminalFanOuterLaneSpacing,
      retainedAngularFanOuterDemand_gate_eq_interface_ray,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive, Port.unitVector,
      PeriodicOrthocrossing.translatePolyline,
      Gadget.unitSubdivisionDirections,
      AxisDirection.segmentLength, AxisDirection.between,
      Cell.add, Cell.scale, slotZero]
  all_goals
    rw [Int.natAbs_mul]
    norm_num
    have slotPositive : 0 < slot.val := Nat.pos_of_ne_zero slotZero
    have slotFinPositive : (0 : RetainedTerminalSlot) < slot := slotPositive
    first | simp [slotFinPositive] | omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
