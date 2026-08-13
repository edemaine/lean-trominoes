/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialRoutes

/-!
# Finite collar routes into the retained angular fan

The unbounded outer radial lanes end on a coordinate-radius-288 square,
while the already-certified fan routes start on a coordinate-radius-264
square.  This file fills the intervening 24-layer collar.

Each direction-and-slot route linearly interpolates its clockwise square
boundary index between those two exact endpoints.  The outer indices reflect
the eleven retained ray slopes; the inner indices are the uniformly spaced
fan-facing ports.  This file certifies the individual finite connectors.
A subsequent coordinated rasterization supplies their pairwise separation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Number of unit square layers between radii 288 and 264. -/
def retainedTerminalFanOuterCollarDepth : Nat :=
  3 * retainedTerminalFanRoutingRefinement

/-- Clockwise boundary index of the base lane for each retained direction
on the radius-288 square. -/
def retainedTerminalFanOuterBoundaryBaseIndex :
    RetainedTerminalDirection → Nat
  | .compass .east => 0
  | .routedClause .left => 128
  | .compass .southeast => 288
  | .compass .south => 576
  | .routedClause .right => 648
  | .compass .southwest => 864
  | .compass .west => 1152
  | .compass .northwest => 1440
  | .compass .north => 1728
  | .compass .northeast => 2016
  | .routedClause .middle => 2232

/-- Clockwise radius-288 boundary index of one outer lane port. -/
def retainedTerminalFanOuterBoundaryIndex
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : Nat :=
  retainedTerminalFanOuterBoundaryBaseIndex direction +
    retainedTerminalFanOuterLaneSpacing * slot.val

/-- Clockwise radius-264 boundary index of the matching fan-facing port. -/
def retainedTerminalFanInnerBoundaryIndex
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : Nat :=
  3 * retainedTerminalFanRoutingRefinement *
    (retainedTerminalFanPort direction slot).val

/-- Rounded boundary index at one radial depth of the outer collar. -/
def retainedTerminalFanOuterCollarBoundaryIndex
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Nat :=
  let totalDepth := retainedTerminalFanOuterCollarDepth
  ((totalDepth - depth) *
        retainedTerminalFanOuterBoundaryIndex direction slot +
      depth *
        retainedTerminalFanInnerBoundaryIndex direction slot +
      totalDepth / 2) /
    totalDepth

/-- Square-boundary sample at one radial depth of the outer collar. -/
def retainedTerminalFanOuterCollarSample
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Cell :=
  retainedTerminalSquareBoundaryPoint
    (36 * retainedTerminalFanRoutingRefinement - depth)
    (retainedTerminalFanOuterCollarBoundaryIndex
      direction slot depth)

/-- The complete outer-collar sample list, including both endpoints. -/
def retainedTerminalFanOuterCollarSamples
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (List.range (retainedTerminalFanOuterCollarDepth + 1)).map
    (retainedTerminalFanOuterCollarSample direction slot)

/-- A centered orthogonal elbow between consecutive collar samples.
Splitting the tangential motion around the radial step shortens each of the
two boundary-parallel pieces. -/
def retainedTerminalFanOuterCollarStep
    (first second : Cell) : List Cell :=
  let radius := max first.1.natAbs first.2.natAbs
  (if first.1.natAbs = radius then
      let middle := (first.2 + second.2) / 2
      [first, (first.1, middle), (second.1, middle), second]
    else
      let middle := (first.1 + second.1) / 2
      [first, (middle, first.2), (middle, second.2), second]).dedup

/-- Join the centered elbows between every consecutive collar sample. -/
def retainedTerminalFanConnectOuterCollarSamples :
    List Cell → List Cell
  | [] => []
  | [point] => [point]
  | first :: second :: rest =>
      joinAtEndpoint
        (retainedTerminalFanOuterCollarStep first second)
        (retainedTerminalFanConnectOuterCollarSamples
          (second :: rest))
termination_by points => points.length

/-- Finite orthogonal collar route from a radius-288 lane port to the
matching radius-264 fan-facing port. -/
def retainedTerminalFanOuterCollarRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanConnectOuterCollarSamples
    (retainedTerminalFanOuterCollarSamples direction slot)

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- The first collar sample is the exact radius-288 outer lane port. -/
theorem retainedTerminalFanOuterCollarSample_zero :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanOuterCollarSample direction slot 0 =
        retainedTerminalFanOuterLanePortOffset direction slot := by
  native_decide

/-- The last collar sample is the exact radius-264 fan-facing port. -/
theorem retainedTerminalFanOuterCollarSample_last :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanOuterCollarSample direction slot
          retainedTerminalFanOuterCollarDepth =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset
            (retainedTerminalFanPort direction slot)) := by
  native_decide

/-- Every collar route starts at its exact outer lane port. -/
@[simp]
theorem retainedTerminalFanOuterCollarRoute_head? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterCollarRoute
        direction slot).head? =
          some
            (retainedTerminalFanOuterLanePortOffset
              direction slot) := by
  native_decide

/-- Every collar route ends at its exact fan-facing port. -/
@[simp]
theorem retainedTerminalFanOuterCollarRoute_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanOuterCollarRoute
        direction slot).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalFanPortOffset
                (retainedTerminalFanPort direction slot))) := by
  native_decide

/-- Every finite outer-collar route is orthogonal. -/
theorem retainedTerminalFanOuterCollarRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanOuterCollarRoute
          direction slot) := by
  native_decide

/-- Every collar point stays within radius 288 and outside radius 263. -/
theorem retainedTerminalFanOuterCollarRoute_points_in_shell :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanOuterCollarRoute direction slot →
        WithinCoordinateRadius 288 (0, 0) point ∧
          ¬ WithinCoordinateRadius 263 (0, 0) point := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
