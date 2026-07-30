import LeanTrominoes.RetainedAngularFanOuterCollarRoutes

/-!
# Coordinated separation in the outer fan collar

The sampled collar routes have strictly ordered endpoints on every square
layer.  To rasterize consecutive samples without contact, each route crosses
to the next layer on the centerline between the preceding route's next
sample and the following route's current sample.  Virtual neighbors extend
the same affine slot pattern just beyond slots zero and seven.

This coordinated elbow choice keeps the full horizontal or vertical trace
of neighboring routes in disjoint strips, including when several retained
terminals have the same direction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Outer boundary index with an unrestricted natural lane number.  Lanes
zero through seven agree with the exact outer collar endpoints; lanes just
outside that interval are used only to place virtual neighboring samples. -/
def retainedTerminalFanOuterBoundaryIndexNat
    (direction : RetainedTerminalDirection)
    (lane : Nat) : Nat :=
  retainedTerminalFanOuterBoundaryBaseIndex direction +
    retainedTerminalFanOuterLaneSpacing * lane

/-- Inner boundary index with an unrestricted natural lane number. -/
def retainedTerminalFanInnerBoundaryIndexNat
    (direction : RetainedTerminalDirection)
    (lane : Nat) : Nat :=
  3 * retainedTerminalFanRoutingRefinement *
    (8 * direction.angularRank + lane)

/-- Interpolated collar boundary index for an unrestricted natural lane. -/
def retainedTerminalFanOuterCollarBoundaryIndexNat
    (direction : RetainedTerminalDirection)
    (lane depth : Nat) : Nat :=
  let totalDepth := retainedTerminalFanOuterCollarDepth
  ((totalDepth - depth) *
        retainedTerminalFanOuterBoundaryIndexNat direction lane +
      depth *
        retainedTerminalFanInnerBoundaryIndexNat direction lane +
      totalDepth / 2) /
    totalDepth

/-- Interpolated square sample for an unrestricted natural lane. -/
def retainedTerminalFanOuterCollarSampleNat
    (direction : RetainedTerminalDirection)
    (lane depth : Nat) : Cell :=
  retainedTerminalSquareBoundaryPoint
    (36 * retainedTerminalFanRoutingRefinement - depth)
    (retainedTerminalFanOuterCollarBoundaryIndexNat
      direction lane depth)

/-- Unrestricted-lane samples recover the original finite-slot samples. -/
theorem retainedTerminalFanOuterCollarSampleNat_eq
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) :
    retainedTerminalFanOuterCollarSampleNat
        direction slot.val depth =
      retainedTerminalFanOuterCollarSample
        direction slot depth := by
  simp [retainedTerminalFanOuterCollarSampleNat,
    retainedTerminalFanOuterCollarSample,
    retainedTerminalFanOuterCollarBoundaryIndexNat,
    retainedTerminalFanOuterCollarBoundaryIndex,
    retainedTerminalFanOuterBoundaryIndexNat,
    retainedTerminalFanOuterBoundaryIndex,
    retainedTerminalFanInnerBoundaryIndexNat,
    retainedTerminalFanInnerBoundaryIndex,
    retainedTerminalFanPort_val]

/-- Tangential coordinate of the virtual preceding route on the next radial
layer. -/
def retainedTerminalFanOuterCollarPreviousInnerCoordinate
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat)
    (horizontalSide : Bool) : Int :=
  let own :=
    retainedTerminalFanOuterCollarSampleNat
      direction slot.val (depth + 1)
  if slot.val = 0 then
    let following :=
      retainedTerminalFanOuterCollarSampleNat
        direction 1 (depth + 1)
    if horizontalSide then
      2 * own.1 - following.1
    else
      2 * own.2 - following.2
  else
    let preceding :=
      retainedTerminalFanOuterCollarSampleNat
        direction (slot.val - 1) (depth + 1)
    if horizontalSide then preceding.1 else preceding.2

/-- Tangential coordinate of the virtual following route on the current
radial layer. -/
def retainedTerminalFanOuterCollarNextOuterCoordinate
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat)
    (horizontalSide : Bool) : Int :=
  let own :=
    retainedTerminalFanOuterCollarSampleNat
      direction slot.val depth
  if slot.val = 7 then
    let preceding :=
      retainedTerminalFanOuterCollarSampleNat
        direction 6 depth
    if horizontalSide then
      2 * own.1 - preceding.1
    else
      2 * own.2 - preceding.2
  else
    let following :=
      retainedTerminalFanOuterCollarSampleNat
        direction (slot.val + 1) depth
    if horizontalSide then following.1 else following.2

/-- Small integer tie-break for crossing lines on consecutive layers. -/
def retainedTerminalFanOuterCollarCrossingPhase
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : Int :=
  let standard : Int := 7 - slot.val
  match direction with
  | .routedClause .left =>
      match slot.val with
      | 0 => 7
      | 1 | 2 => 5
      | _ => standard
  | .compass .southeast =>
      match slot.val with
      | 0 => 7
      | 1 | 2 | 3 => 4
      | 4 => 3
      | 5 => 2
      | 6 => 0
      | _ => -3
  | .compass .west =>
      match slot.val with
      | 0 => 7
      | 1 | 2 => 5
      | _ => standard
  | .routedClause .middle =>
      match slot.val with
      | 0 => 7
      | 1 => 4
      | 2 => 5
      | _ => standard
  | _ => standard

/-- Coordinated elbow between one route's consecutive collar samples. -/
def retainedTerminalFanOuterCollarSeparatedStep
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat)
    (first second : Cell) : List Cell :=
  let radius := max first.1.natAbs first.2.natAbs
  let innerRadius := radius - 1
  let bound : Int := radius
  let phase :=
    retainedTerminalFanOuterCollarCrossingPhase direction slot
  let step := retainedTerminalFanOuterLaneStep direction
  let clockwise :=
    (phase * step.1, phase * step.2)
  if first.1.natAbs = radius then
    if second.1.natAbs = innerRadius then
      let middle :=
        min bound
          (max (-bound)
            ((retainedTerminalFanOuterCollarPreviousInnerCoordinate
                direction slot depth false +
              retainedTerminalFanOuterCollarNextOuterCoordinate
                direction slot depth false) / 2 -
              clockwise.2))
      [first, (first.1, middle), (second.1, middle), second].dedup
    else
      [first, (first.1, second.2), second].dedup
  else
    if second.2.natAbs = innerRadius then
      let middle :=
        min bound
          (max (-bound)
            ((retainedTerminalFanOuterCollarPreviousInnerCoordinate
                direction slot depth true +
              retainedTerminalFanOuterCollarNextOuterCoordinate
                direction slot depth true) / 2 -
              clockwise.1))
      [first, (middle, first.2), (middle, second.2), second].dedup
    else
      [first, (second.1, first.2), second].dedup

/-- Join coordinated elbows while tracking their radial depth. -/
def retainedTerminalFanConnectOuterCollarSeparatedSamples
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    Nat → List Cell → List Cell
  | _, [] => []
  | _, [point] => [point]
  | depth, first :: second :: rest =>
      joinAtEndpoint
        (retainedTerminalFanOuterCollarSeparatedStep
          direction slot depth first second)
        (retainedTerminalFanConnectOuterCollarSeparatedSamples
          direction slot (depth + 1) (second :: rest))
termination_by _ points => points.length

/-- Interpolated coordinated collar route used away from the two sharpest
corner turns. -/
def retainedTerminalFanOuterCollarInterpolatedRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanConnectOuterCollarSeparatedSamples
    direction slot 0
    (retainedTerminalFanOuterCollarSamples direction slot)

/-- Explicit vertex-disjoint corner routes for the retained right arm.
After the staggered top-side exits, the routes use nested tracks outside
the radius-264 frame and enter their own fan ports only on the final
segment. -/
def retainedTerminalFanOuterCollarRightRoute
    (slot : RetainedTerminalSlot) : List Cell :=
  match slot.val with
  | 0 =>
      [(-72, 288), (-79, 288), (-79, 287), (-86, 287),
        (-86, 286), (-93, 286), (-93, 285), (-100, 285),
        (-100, 284), (-107, 284), (-107, 283), (-114, 283),
        (-114, 282), (-121, 282), (-121, 281), (-240, 281),
        (-240, 264)]
  | 1 =>
      [(-80, 288), (-87, 288), (-87, 287), (-94, 287),
        (-94, 286), (-101, 286), (-101, 285), (-108, 285),
        (-108, 284), (-115, 284), (-115, 283), (-122, 283),
        (-122, 282), (-264, 282), (-264, 264)]
  | 2 =>
      [(-88, 288), (-95, 288), (-95, 287), (-102, 287),
        (-102, 286), (-109, 286), (-109, 285), (-116, 285),
        (-116, 284), (-123, 284), (-123, 283), (-265, 283),
        (-265, 240), (-264, 240)]
  | 3 =>
      [(-96, 288), (-103, 288), (-103, 287), (-110, 287),
        (-110, 286), (-117, 286), (-117, 285), (-124, 285),
        (-124, 284), (-266, 284), (-266, 216), (-264, 216)]
  | 4 =>
      [(-104, 288), (-111, 288), (-111, 287), (-118, 287),
        (-118, 286), (-125, 286), (-125, 285), (-267, 285),
        (-267, 192), (-264, 192)]
  | 5 =>
      [(-112, 288), (-119, 288), (-119, 287), (-126, 287),
        (-126, 286), (-268, 286), (-268, 168), (-264, 168)]
  | 6 =>
      [(-120, 288), (-127, 288), (-127, 287), (-269, 287),
        (-269, 144), (-264, 144)]
  | _ =>
      [(-128, 288), (-270, 288), (-270, 120), (-264, 120)]

/-- Explicit vertex-disjoint collar routes for the southwest direction.
Each nested vertical track stays outside the radius-264 frame until its
final horizontal segment reaches the matching fan port. -/
def retainedTerminalFanOuterCollarSouthwestRoute
    (slot : RetainedTerminalSlot) : List Cell :=
  match slot.val with
  | 0 =>
      [(-288, 288), (-265, 288), (-265, 96), (-264, 96)]
  | 1 =>
      [(-288, 280), (-266, 280), (-266, 72), (-264, 72)]
  | 2 =>
      [(-288, 272), (-267, 272), (-267, 48), (-264, 48)]
  | 3 =>
      [(-288, 264), (-268, 264), (-268, 24), (-264, 24)]
  | 4 =>
      [(-288, 256), (-269, 256), (-269, 0), (-264, 0)]
  | 5 =>
      [(-288, 248), (-270, 248), (-270, -24), (-264, -24)]
  | 6 =>
      [(-288, 240), (-271, 240), (-271, -48), (-264, -48)]
  | _ =>
      [(-288, 232), (-272, 232), (-272, -72), (-264, -72)]

/-- Final coordinated collar route.  Two corner-heavy direction families
use explicit nested-track certificates; all other directions use the
interpolated construction. -/
def retainedTerminalFanOuterCollarSeparatedRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  match direction with
  | .routedClause .right =>
      retainedTerminalFanOuterCollarRightRoute slot
  | .compass .southwest =>
      retainedTerminalFanOuterCollarSouthwestRoute slot
  | _ =>
      retainedTerminalFanOuterCollarInterpolatedRoute direction slot

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- Every coordinated collar route starts at its exact radius-288 lane
port. -/
@[simp]
theorem retainedTerminalFanOuterCollarSeparatedRoute_head? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterCollarSeparatedRoute
        direction slot).head? =
          some
            (retainedTerminalFanOuterLanePortOffset
              direction slot) := by
  native_decide

/-- Every coordinated collar route ends at its exact radius-264 fan-facing
port. -/
@[simp]
theorem retainedTerminalFanOuterCollarSeparatedRoute_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterCollarSeparatedRoute
        direction slot).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalFanPortOffset
                (retainedTerminalFanPort direction slot))) := by
  native_decide

/-- Every coordinated collar route is orthogonal. -/
theorem retainedTerminalFanOuterCollarSeparatedRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterCollarSeparatedRoute
          direction slot) := by
  native_decide

/-- Every coordinated route remains in the closed radius-288, open
radius-263 collar. -/
theorem retainedTerminalFanOuterCollarSeparatedRoute_points_in_shell :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈
          retainedTerminalFanOuterCollarSeparatedRoute direction slot →
        WithinCoordinateRadius 288 (0, 0) point ∧
          ¬ WithinCoordinateRadius 263 (0, 0) point := by
  native_decide

/-- Every order-compatible pair of coordinated collar routes is completely
separated, including segment interiors and listed points. -/
theorem retainedTerminalFanOuterCollarSeparatedRoutes_strictlyAvoid :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterCollarSeparatedRoute
            firstDirection firstSlot)
          (retainedTerminalFanOuterCollarSeparatedRoute
            secondDirection secondSlot) := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
