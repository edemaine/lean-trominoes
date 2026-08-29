/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterData
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackPrefixScalingStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackTerminalDataBlockStreamSemantics
import LeanTrominoes.RetainedAngularFanFallbackJoinedDirectionSemantics

/-! # Semantic four-route record blocks for retained carriers -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierFallbackRouteTailRecords

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- Finite carrier metadata plus its positive natural span, in retained-pair
presentation order. -/
structure Geometry where
  horizontal : Bool
  nextSlice : Bool
  span : Nat

def Geometry.prefixBlock (geometry : Geometry) : Bool × Nat :=
  (geometry.horizontal, geometry.span)

/-- Selected retained carriers in global row-major rank order. -/
def selectedGeometries
    (entries : List CarrierFallbackTerminalData.IndexedCarrierEntry) :
    List Geometry :=
  entries.flatMap fun first =>
    entries.flatMap fun second =>
      if CarrierRankOrderedPairs.retainedPredicate first second then
        [{ horizontal := first.1.1.horizontal
           nextSlice := first.1.1.pairNextSlice second.1.1
           span := (second.1.1.orderCoordinate -
             first.1.1.orderCoordinate).toNat }]
      else []

/-- The public carrier fallback policy at one clause-major route position. -/
def routeKind : Nat → Nat → RetainedFallbackFanKind
  | 0, 0 => .escaped
  | 0, 1 => .ordinary
  | 1, 0 => .ordinary
  | 1, 1 => .escaped
  | _, _ => .ordinary

/-- Exact terminal query belonging to one route of a selected carrier. -/
def routeQuery (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) :
    FallbackSuffixDirectionCompiler.Batch.Query :=
  let terminal := carrierLensRouteTerminalData
    geometry.horizontal geometry.span localClauseIndex literalIndex
  { kind := routeKind localClauseIndex literalIndex
    direction := terminal.1
    rawLength := terminal.2
    slot := slot }

/-- Complete scaled source-prefix-plus-retained-fan direction word of one
carrier incidence. -/
def routeDirections (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.repeatDirections 1152
      (carrierLensRoutePrefixDirections
        geometry.horizontal geometry.span localClauseIndex literalIndex) ++
    (routeQuery geometry localClauseIndex literalIndex slot).geometricSuffixDirections

def queryBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  [routeQuery geometry 0 0 first,
    routeQuery geometry 0 1 second,
    routeQuery geometry 1 0 third,
    routeQuery geometry 1 1 fourth]

def routeDirectionBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List (List AxisDirection) :=
  [routeDirections geometry 0 0 first,
    routeDirections geometry 0 1 second,
    routeDirections geometry 1 0 third,
    routeDirections geometry 1 1 fourth]

/-- One retained carrier contributes two binary profiles and four complete
routes in clause-major incidence order. -/
def block (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.Block where
  firstProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (carrierClauseDescriptor
      geometry.horizontal geometry.nextSlice true)
  secondProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (carrierClauseDescriptor
      geometry.horizontal geometry.nextSlice false)
  first := routeDirections geometry 0 0 first
  second := routeDirections geometry 0 1 second
  third := routeDirections geometry 1 0 third
  fourth := routeDirections geometry 1 1 fourth

/-- Consume exactly four occurrence slots for each selected carrier.  The
fallback branches are irrelevant once the direct-source length theorem is
supplied. -/
def blocks : List Geometry → List RetainedTerminalSlot →
    List BinaryRouteTailRecordBatchFormatter.Block
  | geometry :: geometries, first :: second :: third :: fourth :: slots =>
      block geometry first second third fourth :: blocks geometries slots
  | _, _ => []

/-- Consume the same four-slot groups as `blocks`, retaining the aligned
semantic suffix queries. -/
def queryBlocks : List Geometry → List RetainedTerminalSlot →
    List FallbackSuffixDirectionCompiler.Batch.Query
  | geometry :: geometries, first :: second :: third :: fourth :: slots =>
      queryBlock geometry first second third fourth ++
        queryBlocks geometries slots
  | _, _ => []

/-- Prefix/query pairs in the same block zipper and route order. -/
def routePairs : List Geometry → List RetainedTerminalSlot →
    List (List AxisDirection ×
      FallbackSuffixDirectionCompiler.Batch.Query)
  | geometries, slots =>
      (geometries.flatMap fun geometry =>
        CarrierFallbackPrefixScaling.canonicalScaledPrefixWords
          geometry.horizontal geometry.span).zip
        (queryBlocks geometries slots)

end CarrierFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
