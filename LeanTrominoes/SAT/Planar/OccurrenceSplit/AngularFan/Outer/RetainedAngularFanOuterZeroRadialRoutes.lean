/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Outer.RetainedAngularFanOuterRadialPrefixes

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

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

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
        cases port <;> decide +kernel
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

private def zeroRouteSeparationCheck (first second : List Cell) : Bool :=
  segmentBoxesSeparateCheck first second || routesStrictlyAvoidEachOtherCheck first second

private theorem zeroRouteSeparationCheck_sound (first second : List Cell)
    (checked : zeroRouteSeparationCheck first second = true) :
    RoutesStrictlyAvoidEachOther first second := by
  simp only [zeroRouteSeparationCheck, Bool.or_eq_true] at checked
  rcases checked with boxes | exactCheck
  · exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck first second boxes
  · exact (routesStrictlyAvoidEachOtherCheck_eq_true first second).mp exactCheck

private theorem zeroLocalBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.east)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.routedClause (.left)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.southeast)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.south)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.routedClause (.right)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.southwest)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.west)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.northwest)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.north)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.compass (.northeast)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem zeroLocalBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterZeroRadialRoute (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

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
  intro firstDirection secondDirection firstSlot secondSlot directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          zeroRouteSeparationCheck
            (retainedTerminalFanOuterZeroRadialRoute firstDirection firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using zeroLocalBoxes_case10
  exact zeroRouteSeparationCheck_sound _ _
    (checked secondDirection firstSlot secondSlot directionsLe slotsLt)

private theorem localZeroBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.east)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection) ≠ secondDirection ∧ (.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.left)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.southeast)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.south)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection) ≠ secondDirection ∧ (.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.right)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.southwest)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.west)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.northwest)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.north)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection) ≠ secondDirection ∧ (.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.compass (.northeast)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localZeroBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection) ≠ secondDirection ∧ (.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (zeroRouteSeparationCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot))) = true := by
  decide +kernel

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
  intro firstDirection secondDirection firstSlot secondSlot directionsNe directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection ≠ secondDirection →
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          zeroRouteSeparationCheck
            (retainedTerminalFanOuterLocalRoute firstDirection firstSlot)
            (retainedTerminalFanOuterZeroRadialRoute secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localZeroBoxes_case10
  exact zeroRouteSeparationCheck_sound _ _
    (checked secondDirection firstSlot secondSlot directionsNe directionsLe slotsLt)

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
