/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialPrefixes

/-!
# Zero-length outer radial fan routes

Positive retained terminals can have no radial blocks only in one precise
case: a compass terminal of primitive length one.  Its scaled source gate
already lies on the radius-288 interface, so the radial route is just the
finite tangential lane shift.

This file packages that finite route, identifies it with the general radial
route, and exhaustively certifies its order-compatible interactions with the
local fan adapter.  The only bad local-before-zero combinations use the same
direction; duplicate-free terminal profiles rule those combinations out.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A positive terminal has no radial blocks exactly when it is a
length-one compass terminal. -/
theorem retainedTerminalFanOuterRadialLength_eq_zero_iff_of_positive
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    retainedTerminalFanOuterRadialLength terminal = 0 ↔
      ∃ port : OccurrenceSplitRing.Port,
        terminal = (.compass port, 1) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      constructor
      · intro radialZero
        refine ⟨port, ?_⟩
        simp only [Prod.mk.injEq, true_and]
        simp [
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier]
          at radialZero
        omega
      · rintro ⟨otherPort, equal⟩
        simp only [Prod.mk.injEq] at equal
        rcases equal with ⟨_, rfl⟩
        cases port <;> native_decide
  | routedClause arm =>
      constructor
      · intro radialZero
        cases arm <;>
          simp [
            retainedTerminalFanOuterRadialLength,
            retainedTerminalFanTotalRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            retainedTerminalFanRoutingRefinement,
            retainedTerminalInterfaceMultiplier]
            at radialZero <;>
          omega
      · rintro ⟨port, equal⟩
        simp at equal

/-- The finite radius-288 lane shift used when a radial route has no radial
blocks, based at the origin. -/
def retainedTerminalFanOuterZeroRadialRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanOuterLaneShiftRouteAt
    (retainedTerminalFanRefinedInterfaceOffset direction)
    direction slot

/-- Position a zero-block radial route around an arbitrary source center. -/
def retainedTerminalFanOuterZeroRadialRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanOuterZeroRadialRoute direction slot).map
    (Cell.add center)

/-- The general radial route for a length-one compass terminal reduces
exactly to its positioned finite lane shift. -/
theorem retainedTerminalFanOuterRadialRoute_eq_zeroRadialRouteAt
    (center : Cell)
    (port : OccurrenceSplitRing.Port)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterRadialRoute
        center (.compass port, 1) slot =
      retainedTerminalFanOuterZeroRadialRouteAt
        center (.compass port) slot := by
  rw [retainedTerminalFanOuterRadialRoute]
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  cases port <;>
    simp [
      retainedTerminalFanOuterInwardRay,
      retainedTerminalFanOuterRadialLength,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalInterfaceRadialFactor,
      RetainedRay.rasterize, compassRay, oppositePort,
      retainedTerminalFanOuterLaneShiftRouteAt,
      PeriodicOrthocrossing.translatePolyline,
      retainedTerminalFanOuterZeroRadialRouteAt,
      retainedTerminalFanOuterZeroRadialRoute,
      joinAtEndpoint, Cell.add, Cell.scale] <;>
    intro a b _ <;>
    constructor <;>
    omega

/-- An earlier zero-block radial route avoids every later
order-compatible local fan route. -/
theorem retainedTerminalFanOuterZeroRadialRoute_strictlyAvoid_laterLocal :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterZeroRadialRoute
          firstDirection firstSlot)
        (retainedTerminalFanOuterLocalRoute
          secondDirection secondSlot) := by
  native_decide

/-- An earlier local route avoids a later zero-block radial route whenever
their directions differ.  Equal directions are the sole finite obstruction
and cannot occur in a duplicate-free positive profile. -/
theorem retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterZeroRadialRoute :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection ≠ secondDirection →
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterLocalRoute
          firstDirection firstSlot)
        (retainedTerminalFanOuterZeroRadialRoute
          secondDirection secondSlot) := by
  native_decide

/-- Positioned earlier zero-block radial routes avoid positioned later local
routes. -/
theorem retainedTerminalFanOuterZeroRadialRouteAt_strictlyAvoid_laterLocal
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterZeroRadialRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterZeroRadialRoute_strictlyAvoid_laterLocal
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt)
    center

/-- Positioned earlier local routes avoid positioned later zero-block radial
routes of a different direction. -/
theorem retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterZeroRadialRoute
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsNe : firstDirection ≠ secondDirection)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterZeroRadialRouteAt
        center secondDirection secondSlot) := by
  exact RoutesStrictlyAvoidEachOther.map_add
    (retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterZeroRadialRoute
      firstDirection secondDirection firstSlot secondSlot
      directionsNe directionsLe slotsLt)
    center

end PeriodicEightOccurrenceSplit
end LeanTrominoes
