/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairAffineData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Compiled normalized routed-variable pair blocks -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Decode `[boundary, current, next]`, intentionally discarding the boundary
bit and emitting one normalized triple for either cycle case. -/
def normalizedRoutedVariablePairTruthDescriptorBlock :
    List Bool → List FormulaShapeDirectionOrdering.Token
  | [_boundary, currentCycle, nextCycle] =>
      (if currentCycle then routedVariableFullSiteBlock else []) ++
        (if nextCycle then routedVariableFullSiteBlock else [])
  | _ => []

/-- Evaluate the three established affine guards and decode their normalized
descriptor contribution. -/
def compiledNormalizedRoutedVariablePairDescriptorBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  FixedLengthWordEvaluator.output 3
    normalizedRoutedVariablePairTruthDescriptorBlock
    (predicateListTruthValues routedVariablePairAffinePredicates tokens)

/-- Independently evaluate every complete tagged pair block. -/
def compiledNormalizedRoutedVariablePairDescriptorStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    compiledNormalizedRoutedVariablePairDescriptorBlock tokens

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
