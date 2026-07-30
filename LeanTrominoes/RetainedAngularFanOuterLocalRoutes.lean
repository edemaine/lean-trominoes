import LeanTrominoes.RetainedAngularFanOuterCollarSeparatedRoutes

/-!
# Complete finite routes through the retained angular fan

The separated outer collar ends at exactly the head of the previously
certified refined fan route.  This file joins those two finite pieces,
yielding a radius-288 lane-port route all the way to the matching refined
Figure 7 boundary site.

In addition to separation within each piece family, a finite certificate
checks that every collar route strictly avoids every different slot's inner
fan route.  The four resulting pairwise combinations compose into strict
continuous separation of the complete local routes.  Finally the whole
certificate is translated to an arbitrary retained variable center.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- An earlier outer collar route strictly avoids a later
order-compatible complete inner fan route. -/
theorem retainedTerminalFanOuterCollarRoute_strictlyAvoid_laterFanRoute :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterCollarSeparatedRoute
            firstDirection firstSlot)
          (retainedTerminalFanRefinedRoute
            secondDirection secondSlot) := by
  native_decide

/-- An earlier complete inner fan route strictly avoids a later
order-compatible outer collar route. -/
theorem retainedTerminalFanRefinedRoute_strictlyAvoid_laterOuterCollar :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedRoute
            firstDirection firstSlot)
          (retainedTerminalFanOuterCollarSeparatedRoute
            secondDirection secondSlot) := by
  native_decide

/-- Complete finite local route from one radius-288 lane port through the
outer collar and the refined fan to its Figure 7 boundary site. -/
def retainedTerminalFanOuterLocalRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterCollarSeparatedRoute direction slot)
    (retainedTerminalFanRefinedRoute direction slot)

/-- Every complete local route starts at its exact radius-288 lane port. -/
@[simp]
theorem retainedTerminalFanOuterLocalRoute_head?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLocalRoute direction slot).head? =
      some
        (retainedTerminalFanOuterLanePortOffset
          direction slot) := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterCollarSeparatedRoute_head?
      direction slot)

/-- Every complete local route ends at its matching refined Figure 7
boundary site. -/
@[simp]
theorem retainedTerminalFanOuterLocalRoute_getLast?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLocalRoute direction slot).getLast? =
      some
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanBoundaryOffset slot.val)) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanOuterCollarSeparatedRoute_getLast?
      direction slot)
    (retainedTerminalFanRefinedRoute_head? direction slot)
    (retainedTerminalFanRefinedRoute_getLast? direction slot)

/-- Every complete finite local route is orthogonal. -/
theorem retainedTerminalFanOuterLocalRoute_orthogonal
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterLocalRoute direction slot) := by
  exact
    (retainedTerminalFanOuterCollarSeparatedRoute_orthogonal
      direction slot).joinAtEndpoint
      (retainedTerminalFanRefinedRoute_orthogonal direction slot)
      (retainedTerminalFanOuterCollarSeparatedRoute_getLast?
        direction slot)
      (retainedTerminalFanRefinedRoute_head? direction slot)

/-- Every complete local route stays inside the radius-288 frame. -/
theorem retainedTerminalFanOuterLocalRoute_points_within_outer_frame :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanOuterLocalRoute direction slot →
        WithinCoordinateRadius 288 (0, 0) point := by
  native_decide

/-- Every complete local route stays outside the refined Figure 7
interior. -/
theorem retainedTerminalFanOuterLocalRoute_points_outside_fan :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanOuterLocalRoute direction slot →
        ¬ WithinCoordinateRadius
          (12 * retainedTerminalFanRoutingRefinement - 1)
          (0, 0) point := by
  native_decide

/-- Order-compatible complete local routes are strictly separated. -/
theorem retainedTerminalFanOuterLocalRoutes_strictlyAvoidEachOther
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRoute
        firstDirection firstSlot)
      (retainedTerminalFanOuterLocalRoute
        secondDirection secondSlot) := by
  have collarAvoidCollar :=
    retainedTerminalFanOuterCollarSeparatedRoutes_strictlyAvoid
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have collarAvoidSecondFan :=
    retainedTerminalFanOuterCollarRoute_strictlyAvoid_laterFanRoute
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have firstFanAvoidCollar :=
    retainedTerminalFanRefinedRoute_strictlyAvoid_laterOuterCollar
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have fanAvoidFan :=
    retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have completeFirstAvoidCollar :=
    collarAvoidCollar.join_left firstFanAvoidCollar
      (retainedTerminalFanOuterCollarSeparatedRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedRoute_head?
        firstDirection firstSlot)
  have completeFirstAvoidFan :=
    collarAvoidSecondFan.join_left fanAvoidFan
      (retainedTerminalFanOuterCollarSeparatedRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedRoute_head?
        firstDirection firstSlot)
  exact completeFirstAvoidCollar.join_right
    completeFirstAvoidFan
    (retainedTerminalFanOuterCollarSeparatedRoute_getLast?
      secondDirection secondSlot)
    (retainedTerminalFanRefinedRoute_head?
      secondDirection secondSlot)

/-- Translate a complete finite local route to an arbitrary variable
center. -/
def retainedTerminalFanOuterLocalRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanOuterLocalRoute direction slot).map
    (Cell.add center)

/-- A positioned complete route starts at its positioned radius-288 lane
port. -/
@[simp]
theorem retainedTerminalFanOuterLocalRouteAt_head?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLocalRouteAt
      center direction slot).head? =
        some
          (retainedTerminalFanOuterLanePort
            center direction slot) := by
  simp [retainedTerminalFanOuterLocalRouteAt,
    retainedTerminalFanOuterLanePort]

/-- A positioned complete route ends at its positioned refined Figure 7
boundary site. -/
@[simp]
theorem retainedTerminalFanOuterLocalRouteAt_getLast?
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLocalRouteAt
      center direction slot).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  simp [retainedTerminalFanOuterLocalRouteAt]

/-- Positioning preserves orthogonality of a complete finite local route. -/
theorem retainedTerminalFanOuterLocalRouteAt_orthogonal
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterLocalRouteAt
        center direction slot) := by
  exact
    OccurrenceSplitRing.PeriodicOrthocrossing.OrthogonalPolyline.map_add
      (retainedTerminalFanOuterLocalRoute_orthogonal direction slot)
      center

/-- Positioned order-compatible complete local routes remain strictly
separated. -/
theorem retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
    (center : Cell)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  exact
    RoutesStrictlyAvoidEachOther.map_add
      (retainedTerminalFanOuterLocalRoutes_strictlyAvoidEachOther
        firstDirection secondDirection firstSlot secondSlot
        directionsLe slotsLt)
      center

end PeriodicEightOccurrenceSplit
end LeanTrominoes
