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

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

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
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanOuterRadialFinalStub direction slot).head? =
        some (Cell.add (retainedTerminalFanOuterLanePortOffset direction slot) direction.primitive))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

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
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanOuterRadialFinalStub direction slot).getLast? =
        some (retainedTerminalFanOuterLanePortOffset direction slot))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every final primitive stub is orthogonal. -/
theorem retainedTerminalFanOuterRadialFinalStub_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterRadialFinalStub
          direction slot) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (gridPolylineSegments (retainedTerminalFanOuterRadialFinalStub direction slot)).all
        fun segment => decide segment.IsAxisAligned) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq, ← PeriodicOrthocrossing.orthogonalPolyline_iff_segments] using checked

private theorem stubLocalBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.east)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.routedClause (.left)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.southeast)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.south)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.routedClause (.right)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.southwest)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.west)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.northwest)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.north)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.compass (.northeast)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem stubLocalBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterRadialFinalStub (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot))) = true := by
  decide +kernel

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
  intro firstDirection secondDirection firstSlot secondSlot directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          segmentBoxesSeparateCheck
            (retainedTerminalFanOuterRadialFinalStub firstDirection firstSlot)
            (retainedTerminalFanOuterLocalRoute secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using stubLocalBoxes_case10
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked secondDirection firstSlot secondSlot directionsLe slotsLt)

private theorem localStubBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.east)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.left)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.southeast)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.south)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.right)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.southwest)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.west)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.northwest)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.north)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.compass (.northeast)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

private theorem localStubBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot => finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧
          firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck (retainedTerminalFanOuterLocalRoute (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot))) = true := by
  decide +kernel

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
  intro firstDirection secondDirection firstSlot secondSlot directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          segmentBoxesSeparateCheck
            (retainedTerminalFanOuterLocalRoute firstDirection firstSlot)
            (retainedTerminalFanOuterRadialFinalStub secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using localStubBoxes_case10
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked secondDirection firstSlot secondSlot directionsLe slotsLt)

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
