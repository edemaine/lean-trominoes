/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterCollarRoutes
import LeanTrominoes.RetainedAngularFanOuterCollarRouteTable
import LeanTrominoes.OrthogonalPolylineStrictSeparationCheck
import LeanTrominoes.OrthogonalPolylineSegmentBoxCheck

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

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

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
  | depth, first :: rest =>
      match rest with
      | [] => [first]
      | second :: _ =>
          joinAtEndpoint
            (retainedTerminalFanOuterCollarSeparatedStep
              direction slot depth first second)
            (retainedTerminalFanConnectOuterCollarSeparatedSamples
              direction slot (depth + 1) rest)

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
def retainedTerminalFanOuterCollarComputedRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  match direction with
  | .routedClause .right =>
      retainedTerminalFanOuterCollarRightRoute slot
  | .compass .southwest =>
      retainedTerminalFanOuterCollarSouthwestRoute slot
  | _ =>
      retainedTerminalFanOuterCollarInterpolatedRoute direction slot

/-- Coordinated routes with their verified interpolation already evaluated. -/
def retainedTerminalFanOuterCollarSeparatedRoute
    (direction : RetainedTerminalDirection) (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanCachedOuterCollarRoutes direction).getD slot.val []

private theorem retainedTerminalFanCachedOuterCollarRoute_case0 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case1 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case2 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case3 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case4 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case5 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case6 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case7 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.east)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case8 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case9 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case10 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case11 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case12 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case13 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case14 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case15 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.left)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case16 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case17 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case18 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case19 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case20 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case21 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case22 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case23 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southeast)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case24 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case25 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case26 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case27 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case28 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case29 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case30 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case31 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.south)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case32 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case33 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case34 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case35 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case36 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case37 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case38 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case39 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.right)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case40 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case41 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case42 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case43 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case44 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case45 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case46 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case47 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.southwest)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case48 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case49 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case50 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case51 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case52 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case53 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case54 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case55 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.west)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case56 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case57 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case58 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case59 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case60 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case61 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case62 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case63 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northwest)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case64 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case65 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case66 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case67 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case68 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case69 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case70 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case71 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.north)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case72 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case73 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case74 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case75 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case76 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case77 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case78 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case79 :
    retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.compass (.northeast)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case80 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 0 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case81 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 1 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case82 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 2 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case83 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 3 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case84 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 4 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case85 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 5 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case86 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 6 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedOuterCollarRoute_case87 :
    retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) 7 =
      retainedTerminalFanOuterCollarComputedRoute (.routedClause (.middle)) 7 := by
  decide +kernel

/-- Every stored route is exactly the original interpolated orthogonal route. -/
theorem retainedTerminalFanOuterCollarSeparatedRoute_eq_computed
    (direction : RetainedTerminalDirection) (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterCollarSeparatedRoute direction slot =
      retainedTerminalFanOuterCollarComputedRoute direction slot := by
  have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 ∨
      slot.val = 4 ∨ slot.val = 5 ∨ slot.val = 6 ∨ slot.val = 7 := by
    have bound := slot.is_lt
    omega
  rcases cases with h | h | h | h | h | h | h | h
  · have slotEq : slot = 0 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case0
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case16
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case24
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case40
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case48
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case56
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case64
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case72
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case8
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case32
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case80
  · have slotEq : slot = 1 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case1
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case17
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case25
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case41
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case49
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case57
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case65
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case73
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case9
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case33
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case81
  · have slotEq : slot = 2 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case2
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case18
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case26
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case42
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case50
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case58
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case66
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case74
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case10
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case34
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case82
  · have slotEq : slot = 3 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case3
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case19
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case27
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case43
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case51
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case59
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case67
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case75
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case11
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case35
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case83
  · have slotEq : slot = 4 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case4
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case20
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case28
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case44
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case52
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case60
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case68
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case76
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case12
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case36
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case84
  · have slotEq : slot = 5 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case5
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case21
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case29
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case45
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case53
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case61
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case69
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case77
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case13
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case37
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case85
  · have slotEq : slot = 6 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case6
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case22
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case30
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case46
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case54
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case62
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case70
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case78
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case14
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case38
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case86
  · have slotEq : slot = 7 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedOuterCollarRoute_case7
        | southeast => exact retainedTerminalFanCachedOuterCollarRoute_case23
        | south => exact retainedTerminalFanCachedOuterCollarRoute_case31
        | southwest => exact retainedTerminalFanCachedOuterCollarRoute_case47
        | west => exact retainedTerminalFanCachedOuterCollarRoute_case55
        | northwest => exact retainedTerminalFanCachedOuterCollarRoute_case63
        | north => exact retainedTerminalFanCachedOuterCollarRoute_case71
        | northeast => exact retainedTerminalFanCachedOuterCollarRoute_case79
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedOuterCollarRoute_case15
        | right => exact retainedTerminalFanCachedOuterCollarRoute_case39
        | middle => exact retainedTerminalFanCachedOuterCollarRoute_case87

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
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanOuterCollarSeparatedRoute direction slot).head? =
        some (retainedTerminalFanOuterLanePortOffset direction slot))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

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
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanOuterCollarSeparatedRoute direction slot).getLast? =
        some (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset (retainedTerminalFanPort direction slot))))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every coordinated collar route is orthogonal. -/
theorem retainedTerminalFanOuterCollarSeparatedRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterCollarSeparatedRoute
          direction slot) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (gridPolylineSegments (retainedTerminalFanOuterCollarSeparatedRoute direction slot)).all
        fun segment => decide segment.IsAxisAligned) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq,
    ← PeriodicOrthocrossing.orthogonalPolyline_iff_segments] using checked

/-- Every coordinated route remains in the closed radius-288, open
radius-263 collar. -/
theorem retainedTerminalFanOuterCollarSeparatedRoute_points_in_shell :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈
          retainedTerminalFanOuterCollarSeparatedRoute direction slot →
        WithinCoordinateRadius 288 (0, 0) point ∧
          ¬ WithinCoordinateRadius 263 (0, 0) point := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (retainedTerminalFanOuterCollarSeparatedRoute direction slot).all fun point =>
        decide (WithinCoordinateRadius 288 (0, 0) point ∧
          ¬ WithinCoordinateRadius 263 (0, 0) point)) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

private theorem outerCollarSegmentBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.east)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.left)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southeast)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.south)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.right)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.southwest)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.west)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northwest)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.north)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.compass (.northeast)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem outerCollarSegmentBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot))) = true := by
  decide +kernel

/-- Two routes whose outer directions and inner slots occur in the same
strict clockwise order have complete continuous separation. -/
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
  intro firstDirection secondDirection firstSlot secondSlot directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          segmentBoxesSeparateCheck
            (retainedTerminalFanOuterCollarSeparatedRoute firstDirection firstSlot)
            (retainedTerminalFanOuterCollarSeparatedRoute secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using outerCollarSegmentBoxes_case10
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked secondDirection firstSlot secondSlot directionsLe slotsLt)


end PeriodicEightOccurrenceSplit
end LeanTrominoes
