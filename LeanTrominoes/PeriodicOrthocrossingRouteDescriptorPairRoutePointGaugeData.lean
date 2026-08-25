/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegments

/-! # Period gauges of finite affine route templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Drawing-period gauges of the source-fanout points. -/
def FanoutShape.sourcePointGauges : FanoutShape → List Cell
  | .straight => [(0, 0), (0, 0)]
  | .bent => [(0, 0), (0, 0), (0, 0)]

/-- Drawing-period gauge of the translated target endpoint of a core shape. -/
def CoreShape.periodGauge : CoreShape → Cell
  | .zero => (0, 0)
  | .positiveHorizontalDirect | .positiveHorizontalBent => (1, 0)
  | .negativeHorizontalDirect | .negativeHorizontalBent => (-1, 0)
  | .positiveVertical => (0, 1)
  | .negativeVertical => (0, -1)

/-- Drawing-period gauges of the complete core point list. -/
def CoreShape.pointGauges : CoreShape → List Cell
  | .zero =>
      [(0, 0), (0, 0), (0, 0), (0, 0)]
  | .positiveHorizontalDirect =>
      [(0, 0), (0, 0), (1, 0), (1, 0)]
  | .positiveHorizontalBent =>
      [(0, 0), (0, 0), (1, 0), (1, 0), (1, 0), (1, 0)]
  | .negativeHorizontalDirect =>
      [(0, 0), (0, 0), (-1, 0), (-1, 0)]
  | .negativeHorizontalBent =>
      [(0, 0), (0, 0), (0, 0), (0, 0), (-1, 0), (-1, 0)]
  | .positiveVertical =>
      [(0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1)]
  | .negativeVertical =>
      [(0, 0), (0, 0), (0, 0), (0, -1), (0, -1), (0, -1)]

/-- Drawing-period gauges of the translated target-fanout tail. -/
def FanoutShape.targetTailPointGauges
    (shape : FanoutShape) (coreShape : CoreShape) : List Cell :=
  match shape with
  | .straight => [coreShape.periodGauge]
  | .bent => [coreShape.periodGauge, coreShape.periodGauge]

/-- Drawing-period gauges aligned with a complete affine route point list. -/
def routePointGauges
    (sourceShape : FanoutShape) (coreShape : CoreShape)
    (targetShape : FanoutShape) : List Cell :=
  sourceShape.sourcePointGauges ++ coreShape.pointGauges.tail ++
    targetShape.targetTailPointGauges coreShape

/-- Drawing-period gauges aligned with one selected route shape. -/
def RouteShape.pointGauges (shape : RouteShape) : List Cell :=
  routePointGauges shape.source shape.core shape.target

/-- An affine segment together with the drawing-period gauges of its two
endpoints. -/
structure GaugedSegment where
  segment : Segment
  startGauge : Cell
  finishGauge : Cell
  deriving DecidableEq

/-- Consecutive segments of point and gauge lists read in lockstep. -/
def gaugedSegments : List Point → List Cell → List GaugedSegment
  | firstPoint :: secondPoint :: remainingPoints,
      firstGauge :: secondGauge :: remainingGauges =>
      ⟨⟨firstPoint, secondPoint⟩, firstGauge, secondGauge⟩ ::
        gaugedSegments (secondPoint :: remainingPoints)
          (secondGauge :: remainingGauges)
  | _, _ => []

/-- Gauged consecutive segments of one selected route shape. -/
def RouteShape.gaugedSegments
    (shape : RouteShape) (side : RouteDescriptorPairFieldTags.Side) :
    List GaugedSegment :=
  RouteDescriptorPairAffine.gaugedSegments
    (shape.points side) shape.pointGauges

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
