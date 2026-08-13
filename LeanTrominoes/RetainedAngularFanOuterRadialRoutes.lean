/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSpliceInterface
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Radial lanes from retained source gates to the outer fan frame

Several retained incidences can have nested splice gates on one terminal
ray.  At the factor-288 splice scale, there is enough room to give the eight
possible gates parallel tracks.  A gate first moves by a short
clockwise-tangential lane offset, then follows a translated retained-ray
staircase inward to a distinct point on the radius-288 interface square.

The lane spacing is eight.  All eight lanes following one of the eleven
retained directions fit strictly before the next direction's interface
point.  This file defines the unbounded radial part of the outer adapter and
proves its exact endpoints and orthogonality.  Pairwise separation and the
finite radius-288-to-radius-264 connector are handled by the next layer.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Lattice spacing between parallel retained-ray lanes. -/
def retainedTerminalFanOuterLaneSpacing : Nat := 8

/-- Clockwise axis direction along the interface-square side reached by one
retained terminal direction. -/
def retainedTerminalFanOuterLaneStep :
    RetainedTerminalDirection → Cell
  | .compass .east => (0, 1)
  | .routedClause .left => (0, 1)
  | .compass .southeast => (-1, 0)
  | .compass .south => (-1, 0)
  | .routedClause .right => (-1, 0)
  | .compass .southwest => (0, -1)
  | .compass .west => (0, -1)
  | .compass .northwest => (1, 0)
  | .compass .north => (1, 0)
  | .compass .northeast => (0, 1)
  | .routedClause .middle => (0, 1)

/-- Tangential displacement selecting one of eight parallel radial lanes. -/
def retainedTerminalFanOuterLaneOffset
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) : Cell :=
  Cell.scale
    (retainedTerminalFanOuterLaneSpacing * lane.val)
    (retainedTerminalFanOuterLaneStep direction)

/-- Distinct direction-and-lane pairs select distinct points on the refined
radius-288 interface square. -/
def retainedTerminalFanOuterLanePortOffset
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) : Cell :=
  Cell.add
    (retainedTerminalFanRefinedInterfaceOffset direction)
    (retainedTerminalFanOuterLaneOffset direction lane)

/-- Every outer lane port lies exactly on the refined radius-288 square. -/
theorem retainedTerminalFanOuterLanePortOffset_on_square :
    ∀ (direction : RetainedTerminalDirection)
      (lane : RetainedTerminalSlot),
      WithinCoordinateRadius 288 (0, 0)
          (retainedTerminalFanOuterLanePortOffset
            direction lane) ∧
        ¬ WithinCoordinateRadius 287 (0, 0)
          (retainedTerminalFanOuterLanePortOffset
            direction lane) := by
  native_decide

/-- The 88 refined outer lane ports are pairwise distinct. -/
theorem retainedTerminalFanOuterLanePortOffset_injective :
    Function.Injective fun pair :
        RetainedTerminalDirection × RetainedTerminalSlot =>
      retainedTerminalFanOuterLanePortOffset pair.1 pair.2 := by
  native_decide

/-- Positioned outer lane port around an arbitrary retained source center. -/
def retainedTerminalFanOuterLanePort
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) : Cell :=
  Cell.add center
    (retainedTerminalFanOuterLanePortOffset direction lane)

/-- Number of primitive retained-ray steps from a scaled splice gate back to
the refined radius-288 interface. -/
def retainedTerminalFanOuterRadialLength
    (terminal : RetainedTerminalData) : Nat :=
  retainedTerminalFanTotalRefinement * terminal.2 -
    retainedTerminalFanRoutingRefinement *
      retainedTerminalInterfaceMultiplier terminal.1

/-- Forward retained ray that travels from a backwards terminal gate toward
the variable center. -/
def retainedTerminalFanOuterInwardRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  match terminal.1 with
  | .compass port =>
      .compass (oppositePort port)
        (retainedTerminalFanOuterRadialLength terminal)
  | .routedClause arm =>
      .routedClause arm
        (retainedTerminalFanOuterRadialLength terminal)

/-- The finite tangential entrance into a radial lane, based at the origin. -/
def retainedTerminalFanOuterLaneShiftRoute
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) : List Cell :=
  if lane.val = 0 then
    [(0, 0)]
  else
    [(0, 0),
      retainedTerminalFanOuterLaneOffset direction lane]

@[simp]
theorem retainedTerminalFanOuterLaneShiftRoute_head? :
    ∀ (direction : RetainedTerminalDirection)
      (lane : RetainedTerminalSlot),
      (retainedTerminalFanOuterLaneShiftRoute
        direction lane).head? = some (0, 0) := by
  native_decide

@[simp]
theorem retainedTerminalFanOuterLaneShiftRoute_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (lane : RetainedTerminalSlot),
      (retainedTerminalFanOuterLaneShiftRoute
        direction lane).getLast? =
          some
            (retainedTerminalFanOuterLaneOffset
              direction lane) := by
  native_decide

/-- Every finite lane shift is orthogonal. -/
theorem retainedTerminalFanOuterLaneShiftRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (lane : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterLaneShiftRoute
          direction lane) := by
  native_decide

/-- Position the finite lane shift at a scaled source gate. -/
def retainedTerminalFanOuterLaneShiftRouteAt
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) : List Cell :=
  PeriodicOrthocrossing.translatePolyline gate
    (retainedTerminalFanOuterLaneShiftRoute direction lane)

@[simp]
theorem retainedTerminalFanOuterLaneShiftRouteAt_head?
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLaneShiftRouteAt
      gate direction lane).head? = some gate := by
  simp [retainedTerminalFanOuterLaneShiftRouteAt,
    PeriodicOrthocrossing.translatePolyline, Cell.add]

@[simp]
theorem retainedTerminalFanOuterLaneShiftRouteAt_getLast?
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLaneShiftRouteAt
      gate direction lane).getLast? =
        some
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset
              direction lane)) := by
  simp [retainedTerminalFanOuterLaneShiftRouteAt,
    PeriodicOrthocrossing.translatePolyline]

/-- Positioning preserves orthogonality of the finite lane shift. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterLaneShiftRouteAt
        gate direction lane) := by
  exact
    (retainedTerminalFanOuterLaneShiftRoute_orthogonal
      direction lane).translate gate

/-- Radial lane route from one exact scaled source gate to its distinct
radius-288 outer lane port. -/
def retainedTerminalFanOuterRadialRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand
      center terminal lane).gate
  let shiftedGate :=
    Cell.add gate
      (retainedTerminalFanOuterLaneOffset terminal.1 lane)
  joinAtEndpoint
    (retainedTerminalFanOuterLaneShiftRouteAt
      gate terminal.1 lane)
    ((retainedTerminalFanOuterInwardRay terminal).rasterize
      shiftedGate)

/-- Every outer radial route starts at its exact scaled source gate. -/
@[simp]
theorem retainedTerminalFanOuterRadialRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot) :
    (retainedTerminalFanOuterRadialRoute
      center terminal lane).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal lane).gate := by
  apply joinAtEndpoint_head?
  exact retainedTerminalFanOuterLaneShiftRouteAt_head?
    _ terminal.1 lane

set_option maxRecDepth 2048 in
/-- A positive terminal's translated retained-ray staircase ends at the
advertised distinct radius-288 outer lane port. -/
theorem retainedTerminalFanOuterInwardRay_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    ((retainedTerminalFanOuterInwardRay terminal).rasterize
      (Cell.add
        (retainedAngularFanOuterDemand
          center terminal lane).gate
        (retainedTerminalFanOuterLaneOffset
          terminal.1 lane))).getLast? =
      some
        (retainedTerminalFanOuterLanePort
          center terminal.1 lane) := by
  rw [RetainedRay.rasterize_getLast?]
  apply congrArg some
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  rcases center with ⟨centerX, centerY⟩
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        apply Prod.ext <;>
        simp [
          retainedTerminalFanRoutingRefinement,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterLanePort,
          retainedTerminalFanOuterLanePortOffset,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          RetainedTerminalDirection.primitive,
          RetainedRay.vector, oppositePort,
          Port.unitVector, Cell.add, Cell.scale] <;>
        omega
  | routedClause arm =>
      cases arm <;>
        apply Prod.ext <;>
        simp [
          retainedTerminalFanRoutingRefinement,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterLanePort,
          retainedTerminalFanOuterLanePortOffset,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          RetainedTerminalDirection.primitive,
          RetainedRay.vector, routedClauseRayPrimitive,
          Cell.add, Cell.sub, Cell.scale] <;>
        omega

/-- Every positive outer radial route has the exact advertised lane-port
endpoint. -/
@[simp]
theorem retainedTerminalFanOuterRadialRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    (retainedTerminalFanOuterRadialRoute
      center terminal lane).getLast? =
        some
          (retainedTerminalFanOuterLanePort
            center terminal.1 lane) := by
  apply joinAtEndpoint_getLast?
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      _ terminal.1 lane)
    (RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardRay terminal) _)
  exact retainedTerminalFanOuterInwardRay_getLast?
    center terminal lane lengthPositive

/-- Every outer radial route is orthogonal. -/
theorem retainedTerminalFanOuterRadialRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterRadialRoute
        center terminal lane) := by
  apply
    (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      _ terminal.1 lane).joinAtEndpoint
      ((retainedTerminalFanOuterInwardRay terminal).rasterize_orthogonal _)
  · exact retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      _ terminal.1 lane
  · exact RetainedRay.rasterize_head?
      (retainedTerminalFanOuterInwardRay terminal) _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
