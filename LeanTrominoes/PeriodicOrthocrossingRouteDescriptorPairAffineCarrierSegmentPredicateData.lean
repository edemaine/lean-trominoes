/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Lightweight affine carrier-segment predicates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Select the diagonal pair carrying one semantic route descriptor. -/
def carrierSegmentSameEdgeIndex : Predicate :=
  equal (field .first 2) (field .second 2)

/-- Affine test that one selected carrier segment is nondegenerate and
horizontal. -/
def Segment.carrierIsHorizontal (segment : Segment) : Predicate :=
  all [equal segment.start.vertical segment.finish.vertical,
    notEqual segment.start.horizontal segment.finish.horizontal]

/-- Affine test that one selected carrier segment is nondegenerate and
vertical. -/
def Segment.carrierIsVertical (segment : Segment) : Predicate :=
  all [equal segment.start.horizontal segment.finish.horizontal,
    notEqual segment.start.vertical segment.finish.vertical]

/-- Classify one segment of one selected route shape by its axis. -/
def Segment.carrierAxisPredicates
    (shape : RouteShape) (segment : Segment) : List Predicate :=
  [all [carrierSegmentSameEdgeIndex, shape.guard .first,
      segment.carrierIsHorizontal],
    all [carrierSegmentSameEdgeIndex, shape.guard .first,
      segment.carrierIsVertical]]

/-- Axis predicates for all segments of one route shape. -/
def RouteShape.carrierSegmentPredicates
    (shape : RouteShape) : List Predicate :=
  (shape.segments .first).flatMap
    (Segment.carrierAxisPredicates shape)

/-- Complete fixed affine predicate list for base carrier segments. -/
def carrierSegmentPredicates : List Predicate :=
  allRouteShapes.flatMap RouteShape.carrierSegmentPredicates

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
