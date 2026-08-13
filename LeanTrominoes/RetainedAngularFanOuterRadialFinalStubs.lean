/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation

/-!
# Fixed final stubs of outer radial fan routes

An arbitrary-length radial raster can meet the closed radius-288 fan frame
only at its final primitive block.  This file packages that finite block for
all eleven retained directions and certifies its interaction with every
order-compatible local fan route.

The preceding, arbitrary-length part will be separated from the whole local
adapter by a strict supporting half-plane.  These finite certificates handle
the one block between that exterior prefix and the exact lane port.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- One final inward primitive block, based one primitive outside the exact
radius-288 lane port. -/
def retainedTerminalFanOuterRadialFinalStub
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  let start :=
    Cell.add
      (retainedTerminalFanOuterLanePortOffset direction slot)
      direction.primitive
  match direction with
  | .compass port =>
      compassRay (oppositePort port) 1 start
  | .routedClause arm =>
      routedClauseRay arm 1 start

/-- A final stub starts exactly one outward primitive from its lane port. -/
@[simp]
theorem retainedTerminalFanOuterRadialFinalStub_head? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterRadialFinalStub
        direction slot).head? =
          some
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset direction slot)
              direction.primitive) := by
  native_decide

/-- A final stub ends at its exact radius-288 lane port. -/
@[simp]
theorem retainedTerminalFanOuterRadialFinalStub_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterRadialFinalStub
        direction slot).getLast? =
          some
            (retainedTerminalFanOuterLanePortOffset
              direction slot) := by
  native_decide

/-- Every final primitive stub is orthogonal. -/
theorem retainedTerminalFanOuterRadialFinalStub_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterRadialFinalStub
          direction slot) := by
  native_decide

/-- An earlier final radial stub avoids every later order-compatible local
fan route. -/
theorem retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_laterLocal :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterRadialFinalStub
            firstDirection firstSlot)
          (retainedTerminalFanOuterLocalRoute
            secondDirection secondSlot) := by
  native_decide

/-- An earlier local fan route avoids every later order-compatible final
radial stub. -/
theorem retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterFinalStub :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterLocalRoute
            firstDirection firstSlot)
          (retainedTerminalFanOuterRadialFinalStub
            secondDirection secondSlot) := by
  native_decide

/-- Position a final radial stub around an arbitrary retained source
center. -/
def retainedTerminalFanOuterRadialFinalStubAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanOuterRadialFinalStub direction slot).map
    (Cell.add center)

/-- A positioned final stub starts one primitive outside its positioned
lane port. -/
@[simp]
theorem retainedTerminalFanOuterRadialFinalStubAt_head?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterRadialFinalStubAt
      center direction slot).head? =
        some
          (Cell.add center
            (Cell.add
              (retainedTerminalFanOuterLanePortOffset direction slot)
              direction.primitive)) := by
  simp [retainedTerminalFanOuterRadialFinalStubAt]

/-- A positioned final stub ends at its positioned radius-288 lane port. -/
@[simp]
theorem retainedTerminalFanOuterRadialFinalStubAt_getLast?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterRadialFinalStubAt
      center direction slot).getLast? =
        some
          (retainedTerminalFanOuterLanePort
            center direction slot) := by
  simp [retainedTerminalFanOuterRadialFinalStubAt,
    retainedTerminalFanOuterLanePort]

/-- Positioning preserves final-stub orthogonality. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_orthogonal
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterRadialFinalStubAt
        center direction slot) := by
  exact
    OccurrenceSplitRing.PeriodicOrthocrossing.OrthogonalPolyline.map_add
      (retainedTerminalFanOuterRadialFinalStub_orthogonal direction slot)
      center

/-- Positioned earlier final stubs avoid positioned later local routes. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_laterLocal
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialFinalStubAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterRadialFinalStub_strictlyAvoid_laterLocal
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    center

/-- Positioned earlier local routes avoid positioned later final stubs. -/
theorem retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterFinalStub
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterRadialFinalStubAt
        center secondDirection secondSlot) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterFinalStub
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    center

end PeriodicEightOccurrenceSplit
end LeanTrominoes
