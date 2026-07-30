import LeanTrominoes.RetainedAngularFanAnnulusRoutes
import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Coordinated refined routes across the retained fan annulus

The base annulus is uniformly refined by eight.  At each successive square
radius, a route linearly interpolates its normalized clockwise coordinate
between the direction-and-slot outer port and the fixed compass anchor.
Successive samples are joined by a side-following orthogonal elbow.

The factor-eight spacing is large enough that every two order-compatible
routes are strictly separated.  This is checked over the finite set of
eleven retained directions and eight slots, rather than over the much larger
raw terminal-shape type.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Uniform local refinement used by the coordinated annular router. -/
def retainedTerminalFanRoutingRefinement : Nat := 8

/-- Number of unit radial layers between the refined radius-33 and radius-22
frames. -/
def retainedTerminalFanRoutingDepth : Nat :=
  11 * retainedTerminalFanRoutingRefinement

/-- Clockwise point at a unit boundary index on a square of the given
coordinate radius. -/
def retainedTerminalSquareBoundaryPoint
    (radius index : Nat) : Cell :=
  let r : Int := radius
  let q : Int := index
  if index ≤ radius then
    (r, q)
  else if index ≤ 3 * radius then
    (2 * r - q, r)
  else if index ≤ 5 * radius then
    (-r, 4 * r - q)
  else if index ≤ 7 * radius then
    (q - 6 * r, -r)
  else
    (r, q - 8 * r)

/-- Rounded clockwise boundary index of one route at a radial depth. -/
def retainedTerminalFanRoutingBoundaryIndex
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Nat :=
  let totalDepth := retainedTerminalFanRoutingDepth
  let radius :=
    33 * retainedTerminalFanRoutingRefinement - depth
  let outerIndex :=
    8 * direction.angularRank + slot.val
  let angularNumerator :=
    (totalDepth - depth) * outerIndex +
      11 * depth * slot.val
  let denominator := 88 * totalDepth
  (8 * radius * angularNumerator + denominator / 2) /
    denominator

/-- Refined square-boundary sample of one interpolated annular route. -/
def retainedTerminalFanRoutingSample
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Cell :=
  retainedTerminalSquareBoundaryPoint
    (33 * retainedTerminalFanRoutingRefinement - depth)
    (retainedTerminalFanRoutingBoundaryIndex
      direction slot depth)

/-- Orthogonal elbow between consecutive interpolated samples.  On a
vertical square side it moves vertically first; on a horizontal side it
moves horizontally first. -/
def retainedTerminalFanRoutingStep
    (first second : Cell) : List Cell :=
  let radius := max first.1.natAbs first.2.natAbs
  (if first.1.natAbs = radius then
      [first, (first.1, second.2), second]
    else
      [first, (second.1, first.2), second]).dedup

/-- Join the elbows between every consecutive pair of samples. -/
def retainedTerminalFanConnectSamples : List Cell → List Cell
  | [] => []
  | [point] => [point]
  | first :: second :: rest =>
      joinAtEndpoint
        (retainedTerminalFanRoutingStep first second)
        (retainedTerminalFanConnectSamples (second :: rest))
termination_by points => points.length

/-- The refined sample list from the outer frame through the inner frame. -/
def retainedTerminalFanRoutingSamples
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (List.range (retainedTerminalFanRoutingDepth + 1)).map
    (retainedTerminalFanRoutingSample direction slot)

/-- Coordinated finite annular route selected by a direction and occurrence
slot. -/
def retainedTerminalFanRefinedAnnulusRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanConnectSamples
    (retainedTerminalFanRoutingSamples direction slot)

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- The first interpolated sample is the factor-eight refinement of the
exact radius-33 fan port. -/
theorem retainedTerminalFanRoutingSample_zero :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanRoutingSample direction slot 0 =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset
            (retainedTerminalFanPort direction slot)) := by
  native_decide

/-- The last interpolated sample is the factor-eight refinement of the exact
radius-22 compass anchor. -/
theorem retainedTerminalFanRoutingSample_last :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanRoutingSample direction slot
          retainedTerminalFanRoutingDepth =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalAdapterPortOffset
            (retainedTerminalFanAnchorPort slot)) := by
  native_decide

/-- Every coordinated route starts at its exact refined fan-facing port. -/
@[simp]
theorem retainedTerminalFanRefinedAnnulusRoute_head? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanRefinedAnnulusRoute
        direction slot).head? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalFanPortOffset
                (retainedTerminalFanPort direction slot))) := by
  native_decide

/-- Every coordinated route ends at its exact refined compass anchor. -/
@[simp]
theorem retainedTerminalFanRefinedAnnulusRoute_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanRefinedAnnulusRoute
        direction slot).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalAdapterPortOffset
                (retainedTerminalFanAnchorPort slot))) := by
  native_decide

/-- Every coordinated route is an orthogonal polyline. -/
theorem retainedTerminalFanRefinedAnnulusRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanRefinedAnnulusRoute direction slot) := by
  native_decide

/-- Every listed route point stays inside the refined radius-33 frame and
outside the refined radius-22 fan-anchor frame, except for its inner endpoint
on that frame. -/
theorem retainedTerminalFanRefinedAnnulusRoute_points_in_shell :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedAnnulusRoute direction slot →
        WithinCoordinateRadius
            (33 * retainedTerminalFanRoutingRefinement)
            (0, 0) point ∧
          ¬ WithinCoordinateRadius
            (22 * retainedTerminalFanRoutingRefinement - 1)
            (0, 0) point := by
  native_decide

/-- Two routes whose outer directions and inner slots occur in the same
strict clockwise order have complete continuous separation. -/
theorem retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnnulusRoute
            firstDirection firstSlot)
          (retainedTerminalFanRefinedAnnulusRoute
            secondDirection secondSlot) := by
  native_decide

/-- Factor-eight refinement of the fixed inward compass-anchor route. -/
def retainedTerminalFanRefinedAnchorRoute
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanAnchorRoute slot).map
    (Cell.scale retainedTerminalFanRoutingRefinement)

/-- A refined anchor route starts at the refined radius-22 anchor. -/
@[simp]
theorem retainedTerminalFanRefinedAnchorRoute_head? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanRefinedAnchorRoute slot).head? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (retainedTerminalAdapterPortOffset
              (retainedTerminalFanAnchorPort slot))) := by
  native_decide

/-- A refined anchor route ends at the matching refined Figure 7 boundary
site. -/
@[simp]
theorem retainedTerminalFanRefinedAnchorRoute_getLast? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanRefinedAnchorRoute slot).getLast? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val)) := by
  native_decide

/-- Every refined inward anchor route is orthogonal. -/
theorem retainedTerminalFanRefinedAnchorRoute_orthogonal :
    ∀ slot : RetainedTerminalSlot,
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanRefinedAnchorRoute slot) := by
  native_decide

/-- Different refined inward anchor routes are strictly separated. -/
theorem retainedTerminalFanRefinedAnchorRoutes_strictlyAvoidEachOther :
    ∀ first second : RetainedTerminalSlot,
      first ≠ second →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnchorRoute first)
          (retainedTerminalFanRefinedAnchorRoute second) := by
  native_decide

/-- An annular route is strictly separated from every other slot's inward
anchor route. -/
theorem retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor :
    ∀ (direction : RetainedTerminalDirection)
      (annulusSlot anchorSlot : RetainedTerminalSlot),
      annulusSlot ≠ anchorSlot →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnnulusRoute
            direction annulusSlot)
          (retainedTerminalFanRefinedAnchorRoute anchorSlot) := by
  native_decide

/-- Complete refined route from one occurrence-ordered fan port to the
matching refined Figure 7 boundary site. -/
def retainedTerminalFanRefinedRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanRefinedAnnulusRoute direction slot)
    (retainedTerminalFanRefinedAnchorRoute slot)

/-- Every complete refined route starts at its refined fan-facing port. -/
@[simp]
theorem retainedTerminalFanRefinedRoute_head?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRoute direction slot).head? =
      some
        (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset
            (retainedTerminalFanPort direction slot))) := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanRefinedAnnulusRoute_head?
      direction slot)

/-- Every complete refined route ends at its matching refined Figure 7
boundary site. -/
@[simp]
theorem retainedTerminalFanRefinedRoute_getLast?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRoute direction slot).getLast? =
      some
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanBoundaryOffset slot.val)) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanRefinedAnnulusRoute_getLast?
      direction slot)
    (retainedTerminalFanRefinedAnchorRoute_head? slot)
    (retainedTerminalFanRefinedAnchorRoute_getLast? slot)

/-- Every complete refined fan route is orthogonal. -/
theorem retainedTerminalFanRefinedRoute_orthogonal
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanRefinedRoute direction slot) := by
  exact
    PeriodicOrthocrossing.OrthogonalPolyline.joinAtEndpoint
      (retainedTerminalFanRefinedAnnulusRoute_orthogonal
        direction slot)
      (retainedTerminalFanRefinedAnchorRoute_orthogonal slot)
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        direction slot)
      (retainedTerminalFanRefinedAnchorRoute_head? slot)

/-- Every listed point of a complete refined route remains outside the
interior of the refined radius-12 Figure 7 square. -/
theorem retainedTerminalFanRefinedRoute_points_outside_fan :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedRoute direction slot →
        ¬ WithinCoordinateRadius
          (12 * retainedTerminalFanRoutingRefinement - 1)
          (0, 0) point := by
  native_decide

/-- Every listed point of a complete refined route remains inside the
refined radius-33 outer frame. -/
theorem retainedTerminalFanRefinedRoute_points_within_outer_frame :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedRoute direction slot →
        WithinCoordinateRadius
          (33 * retainedTerminalFanRoutingRefinement)
          (0, 0) point := by
  native_decide

/-- Complete refined routes with order-compatible endpoints are strictly
separated. -/
theorem retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedRoute
        firstDirection firstSlot)
      (retainedTerminalFanRefinedRoute
        secondDirection secondSlot) := by
  have slotsNe : firstSlot ≠ secondSlot := by
    intro slotsEq
    subst secondSlot
    exact Nat.lt_irrefl _ slotsLt
  have annulusAvoidAnnulus :=
    retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have annulusAvoidSecondAnchor :=
    retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor
      firstDirection firstSlot secondSlot slotsNe
  have firstAnchorAvoidAnnulus :=
    (retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor
      secondDirection secondSlot firstSlot slotsNe.symm).symm
  have anchorsAvoid :=
    retainedTerminalFanRefinedAnchorRoutes_strictlyAvoidEachOther
      firstSlot secondSlot slotsNe
  have completeFirstAvoidAnnulus :=
    annulusAvoidAnnulus.join_left firstAnchorAvoidAnnulus
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedAnchorRoute_head? firstSlot)
  have completeFirstAvoidAnchor :=
    annulusAvoidSecondAnchor.join_left anchorsAvoid
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedAnchorRoute_head? firstSlot)
  exact completeFirstAvoidAnnulus.join_right
    completeFirstAvoidAnchor
    (retainedTerminalFanRefinedAnnulusRoute_getLast?
      secondDirection secondSlot)
    (retainedTerminalFanRefinedAnchorRoute_head? secondSlot)

/-- Optional coordinated annular route selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanRefinedAnnulusRoute
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Option (List Cell) :=
  (shape.direction slot).map fun direction =>
    retainedTerminalFanRefinedAnnulusRoute direction slot

/-- Active slots select their exact direction-and-slot route. -/
theorem RetainedAngularTerminalShape.fanRefinedAnnulusRoute_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq : shape.direction slot = some direction) :
    shape.fanRefinedAnnulusRoute slot =
      some
        (retainedTerminalFanRefinedAnnulusRoute
          direction slot) := by
  simp [fanRefinedAnnulusRoute, directionEq]

/-- Distinct active routes of a valid finite shape are strictly separated. -/
theorem RetainedAngularTerminalShape.fanRefinedAnnulusRoutes_strictlyAvoid
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedAnnulusRoute
        firstDirection first)
      (retainedTerminalFanRefinedAnnulusRoute
        secondDirection second) := by
  exact
    retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther
      firstDirection secondDirection first second
      (valid.2.1 first second firstDirection secondDirection
        slotsLt firstDirectionEq secondDirectionEq)
      slotsLt

/-- Optional complete refined fan route selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanRefinedRoute
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Option (List Cell) :=
  (shape.direction slot).map fun direction =>
    retainedTerminalFanRefinedRoute direction slot

/-- An active slot selects its complete exact direction-and-slot route. -/
theorem RetainedAngularTerminalShape.fanRefinedRoute_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq : shape.direction slot = some direction) :
    shape.fanRefinedRoute slot =
      some
        (retainedTerminalFanRefinedRoute direction slot) := by
  simp [fanRefinedRoute, directionEq]

/-- An inactive slot selects no complete refined route. -/
theorem RetainedAngularTerminalShape.fanRefinedRoute_eq_none
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (directionEq : shape.direction slot = none) :
    shape.fanRefinedRoute slot = none := by
  simp [fanRefinedRoute, directionEq]

/-- Complete routes of distinct active slots in a valid shape are strictly
separated. -/
theorem RetainedAngularTerminalShape.fanRefinedRoutes_strictlyAvoid
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedRoute
        firstDirection first)
      (retainedTerminalFanRefinedRoute
        secondDirection second) := by
  exact retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
    firstDirection secondDirection first second
    (valid.2.1 first second firstDirection secondDirection
      slotsLt firstDirectionEq secondDirectionEq)
    slotsLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes
