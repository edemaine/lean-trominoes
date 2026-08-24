/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingNeighborTranslationsData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamData

/-! # Affine base carrier-segment bit scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- One current-slice carrier bit for each fixed neighboring translation of
a horizontal or vertical segment occurrence. -/
def carrierAxisNeighborBlocks : List (List (Bool × Bool)) :=
  [neighborTranslations.map fun _ => (true, false),
    neighborTranslations.map fun _ => (false, false)]

/-- Aligned neighboring-occurrence bit blocks for all segments of one route
shape. -/
def RouteShape.carrierSegmentBitBlocks
    (shape : RouteShape) : List (List (Bool × Bool)) :=
  (shape.segments .first).flatMap fun _ => carrierAxisNeighborBlocks

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
