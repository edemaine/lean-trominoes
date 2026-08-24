/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingNeighborTranslationsData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Affine base carrier-segment bit scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Select the diagonal pair carrying one semantic route descriptor. -/
def carrierSegmentSameEdgeIndex : Predicate :=
  equal (field .first 2) (field .second 2)

/-- Affine test that one selected carrier segment is nondegenerate and
horizontal.  This local form keeps the carrier scan independent of the much
larger crossing-enumeration development. -/
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

/-- One current-slice carrier bit for each fixed neighboring translation of
a horizontal or vertical segment occurrence. -/
def carrierAxisNeighborBlocks : List (List (Bool × Bool)) :=
  [neighborTranslations.map fun _ => (true, false),
    neighborTranslations.map fun _ => (false, false)]

/-- Axis predicates for all segments of one route shape. -/
def RouteShape.carrierSegmentPredicates
    (shape : RouteShape) : List Predicate :=
  (shape.segments .first).flatMap
    (Segment.carrierAxisPredicates shape)

/-- Aligned neighboring-occurrence bit blocks for all segments of one route
shape. -/
def RouteShape.carrierSegmentBitBlocks
    (shape : RouteShape) : List (List (Bool × Bool)) :=
  (shape.segments .first).flatMap fun _ => carrierAxisNeighborBlocks

/-- Complete fixed affine predicate list for base carrier segments. -/
def carrierSegmentPredicates : List Predicate :=
  allRouteShapes.flatMap RouteShape.carrierSegmentPredicates

/-- Complete fixed output blocks aligned with `carrierSegmentPredicates`. -/
def carrierSegmentBitBlocks : List (List (Bool × Bool)) :=
  allRouteShapes.flatMap RouteShape.carrierSegmentBitBlocks

/-- Neighboring segment-occurrence axis bits selected from one tagged route-
descriptor pair.  The second bit is provisionally current-slice; periodic
ownership is handled by the later carrier-link scan. -/
def affineCarrierSegmentBitBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List (Bool × Bool) :=
  predicateListBlocks carrierSegmentPredicates
    carrierSegmentBitBlocks tokens

/-- Pair-major affine scan of all neighboring base segment occurrences. -/
def affineCarrierSegmentBitStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List (Bool × Bool) :=
  predicateListBlockStream carrierSegmentPredicates
    carrierSegmentBitBlocks tokens

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
