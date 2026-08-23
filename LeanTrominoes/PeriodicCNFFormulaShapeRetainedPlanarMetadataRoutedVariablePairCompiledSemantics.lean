/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairAffineSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics

/-! # Exact semantics of compiled routed-variable pair blocks -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

@[simp] theorem routedVariablePairPredicateTruthValues_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    predicateListTruthValues routedVariablePairAffinePredicates
        (descriptorPairTokens pair) =
      [routedVariableNextBoundaryPair pair,
        routedVariableCurrentCyclePair pair,
        routedVariableNextCyclePair pair] := by
  rw [predicateListTruthValues_eq]
  calc
    routedVariablePairAffinePredicates.map
          (fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)) =
        routedVariablePairAffinePredicates.map
          (fun predicate => predicate.evalPair pair) := by
      apply List.map_congr_left
      intro predicate _predicateMember
      exact Predicate.evalTokens_descriptorPairTokens predicate pair
    _ = _ := routedVariablePairAffinePredicates_map_evalPair pair

/-- The compiled three-predicate evaluator emits exactly the semantic finite
block for every canonical ordered descriptor pair. -/
@[simp] theorem compiledRoutedVariablePairDescriptorBlock_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    compiledRoutedVariablePairDescriptorBlock
        (descriptorPairTokens pair) =
      routedVariablePairDescriptorBlock pair := by
  unfold compiledRoutedVariablePairDescriptorBlock
  rw [routedVariablePairPredicateTruthValues_descriptorPairTokens]
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq
    3 routedVariablePairTruthDescriptorBlock _ (by simp)]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
