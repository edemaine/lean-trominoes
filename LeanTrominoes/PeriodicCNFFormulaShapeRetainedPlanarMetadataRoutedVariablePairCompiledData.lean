/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairAffineData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler

/-! # Compiled finite block for one routed-variable descriptor pair -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Decode the fixed `[boundary, current, next]` truth word into the exact
descriptor block contributed by one ordered route pair. -/
def routedVariablePairTruthDescriptorBlock :
    List Bool → List FormulaShapeDirectionOrdering.Token
  | [boundary, currentCycle, nextCycle] =>
      (if boundary then routedVariableNextBoundaryBlock else []) ++
        (if currentCycle then routedVariableCurrentCycleBlock else []) ++
        (if nextCycle then routedVariableNextCycleBlock else [])
  | _ => []

/-- Evaluate all three affine guards for one tagged pair block, then decode
their fixed truth word into routed-variable descriptors. -/
def compiledRoutedVariablePairDescriptorBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  FixedLengthWordEvaluator.output 3
    routedVariablePairTruthDescriptorBlock
    (predicateListTruthValues routedVariablePairAffinePredicates tokens)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
