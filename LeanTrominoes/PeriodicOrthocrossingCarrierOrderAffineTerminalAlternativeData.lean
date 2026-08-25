/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData

/-! # Direction-split terminal order-coordinate candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- The eighteen terminal expressions of one axis and fixed direction. -/
def Segment.terminalDirectionalOrderExpressionBlock
    (segment : Segment) (horizontal increasing : Bool) : List Expression :=
  neighborTranslations.flatMap fun translate =>
    [segment.terminalOrderExpressionForDirection
        horizontal translate .start increasing,
      segment.terminalOrderExpressionForDirection
        horizontal translate .finish increasing]

/-- Decreasing and increasing alternatives for each of the horizontal and
vertical classifications of one segment. -/
def Segment.terminalDirectionalOrderExpressionBlocks
    (segment : Segment) : List (List Expression) :=
  [segment.terminalDirectionalOrderExpressionBlock true false,
    segment.terminalDirectionalOrderExpressionBlock true true,
    segment.terminalDirectionalOrderExpressionBlock false false,
    segment.terminalDirectionalOrderExpressionBlock false true]

/-- Axis/shape support conjoined with the selected segment direction. -/
def Segment.terminalDirectionalPredicates
    (shape : RouteShape) (segment : Segment) : List Predicate :=
  let horizontal := all [carrierSegmentSameEdgeIndex, shape.guard .first,
    segment.carrierIsHorizontal]
  let vertical := all [carrierSegmentSameEdgeIndex, shape.guard .first,
    segment.carrierIsVertical]
  let horizontalIncreasing := segment.increasingPredicate true
  let verticalIncreasing := segment.increasingPredicate false
  [.conjunction horizontal (.negation horizontalIncreasing),
    .conjunction horizontal horizontalIncreasing,
    .conjunction vertical (.negation verticalIncreasing),
    .conjunction vertical verticalIncreasing]

/-- Repeat the ordinary terminal-key block for all four axis/direction
alternatives. -/
def Segment.terminalDirectionalCarrierKeyRecipeBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List Recipe) :=
  let block := segment.terminalCarrierKeyRecipeBlock segmentIndex
  [block, block, block, block]

/-- Repeat the doubled compact source-identity recipe block for all four
axis/direction alternatives.  The adjacent component recipes will later be
merged back to one source-identity word per order-coordinate candidate. -/
def Segment.terminalDirectionalSourceKeyRecipeBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List Recipe) :=
  let block := segment.terminalSourceKeyRecipeBlock segmentIndex
  [block, block, block, block]

def RouteShape.terminalDirectionalOrderExpressionBlocks
    (shape : RouteShape) : List (List Expression) :=
  (shape.segments .first).flatMap
    Segment.terminalDirectionalOrderExpressionBlocks

def RouteShape.terminalDirectionalPredicates
    (shape : RouteShape) : List Predicate :=
  (shape.segments .first).flatMap
    (Segment.terminalDirectionalPredicates shape)

def RouteShape.terminalDirectionalCarrierKeyRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalDirectionalCarrierKeyRecipeBlocks tagged.2

def RouteShape.terminalDirectionalSourceKeyRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalDirectionalSourceKeyRecipeBlocks tagged.2

/-- Complete direction-split terminal candidate families in one shared
fixed order. -/
def terminalDirectionalOrderExpressionBlocks : List (List Expression) :=
  allRouteShapes.flatMap
    RouteShape.terminalDirectionalOrderExpressionBlocks

def terminalDirectionalPredicates : List Predicate :=
  allRouteShapes.flatMap RouteShape.terminalDirectionalPredicates

def terminalDirectionalCarrierKeyRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap
    RouteShape.terminalDirectionalCarrierKeyRecipeBlocks

def terminalDirectionalSourceKeyRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap
    RouteShape.terminalDirectionalSourceKeyRecipeBlocks

def terminalDirectionalOrderExpressions : List Expression :=
  terminalDirectionalOrderExpressionBlocks.flatten

/-- Guarded key words in the same direction-split order as the affine
coordinate expressions. -/
def terminalDirectionalCarrierKeyGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  words tokens
    (terminalDirectionalPredicates.map
      fun predicate => predicate.evalTokens tokens)
    terminalDirectionalCarrierKeyRecipeBlocks

/-- Guarded adjacent source-key components in the same direction-split order
as the affine coordinate expressions. -/
def terminalDirectionalSourceKeyGuardedComponentWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  words tokens
    (terminalDirectionalPredicates.map
      fun predicate => predicate.evalTokens tokens)
    terminalDirectionalSourceKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
