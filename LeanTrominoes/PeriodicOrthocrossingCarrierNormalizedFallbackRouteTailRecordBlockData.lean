/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanNormalizedFallbackJoinedDirectionAllSemantics

/-! # Normalized semantic four-route record blocks for retained carriers -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierNormalizedFallbackRouteTailRecords

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open CarrierFallbackRouteTailRecords

/-- The scaled carrier prefix followed by the canonical normalized retained-fan
suffix selected by one occurrence slot. -/
def routeDirections (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.repeatDirections 1152
      (carrierLensRoutePrefixDirections
        geometry.horizontal geometry.span localClauseIndex literalIndex) ++
    NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedSuffixDirections
      (CarrierFallbackRouteTailRecords.routeQuery geometry
        localClauseIndex literalIndex slot)

def routeDirectionBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List (List AxisDirection) :=
  [routeDirections geometry 0 0 first,
    routeDirections geometry 0 1 second,
    routeDirections geometry 1 0 third,
    routeDirections geometry 1 1 fourth]

/-- The normalized carrier block has the same two profiles as the raw semantic
block and stores its four canonical normalized complete route words. -/
def block (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.Block where
  firstProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (carrierClauseDescriptor geometry.horizontal geometry.nextSlice true)
  secondProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (carrierClauseDescriptor geometry.horizontal geometry.nextSlice false)
  first := routeDirections geometry 0 0 first
  second := routeDirections geometry 0 1 second
  third := routeDirections geometry 1 0 third
  fourth := routeDirections geometry 1 1 fourth

/-- Consume the same four-slot groups as the raw carrier blocks. -/
def blocks : List Geometry → List RetainedTerminalSlot →
    List BinaryRouteTailRecordBatchFormatter.Block
  | geometry :: geometries, first :: second :: third :: fourth :: slots =>
      block geometry first second third fourth :: blocks geometries slots
  | _, _ => []

end CarrierNormalizedFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
