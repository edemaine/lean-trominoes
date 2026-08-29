/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanNormalizedFallbackJoinedDirectionSemantics

/-! # Normalized semantic four-route record blocks for retained bends -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace BendNormalizedFallbackRouteTailRecords

open PlanarThreeSAT
open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open BendFallbackRouteTailRecords

/-- The scaled bend prefix followed by its canonical normalized ordinary
retained-fan suffix. -/
def routeDirections (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.repeatDirections 1152
      (bendRoutePrefixDirections geometry.firstPort geometry.secondPort
        localClauseIndex literalIndex) ++
    NormalizedFallbackSuffixDirectionCompiler.Batch.Query.normalizedOrdinarySuffixDirections
      (BendFallbackRouteTailRecords.routeQuery geometry
        localClauseIndex literalIndex slot)

def routeDirectionBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List (List AxisDirection) :=
  [routeDirections geometry 0 0 first,
    routeDirections geometry 0 1 second,
    routeDirections geometry 1 0 third,
    routeDirections geometry 1 1 fourth]

/-- The normalized bend block preserves the raw semantic profiles and replaces
the four route fields by canonical normalized complete words. -/
def block (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.Block where
  firstProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (bendClauseDescriptor geometry.firstPort geometry.secondPort false true)
  secondProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (bendClauseDescriptor geometry.firstPort geometry.secondPort false false)
  first := routeDirections geometry 0 0 first
  second := routeDirections geometry 0 1 second
  third := routeDirections geometry 1 0 third
  fourth := routeDirections geometry 1 1 fourth

/-- Consume the same four-slot groups as the raw bend blocks. -/
def blocks : List Geometry → List RetainedTerminalSlot →
    List BinaryRouteTailRecordBatchFormatter.Block
  | geometry :: geometries, first :: second :: third :: fourth :: slots =>
      block geometry first second third fourth :: blocks geometries slots
  | _, _ => []

end BendNormalizedFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
