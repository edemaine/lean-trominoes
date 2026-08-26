/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of compiled normalized routed-variable pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

@[simp] theorem
    compiledNormalizedRoutedVariablePairDescriptorBlock_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) :
    compiledNormalizedRoutedVariablePairDescriptorBlock
        (descriptorPairTokens pair) =
      normalizedRoutedVariablePairDescriptorBlock pair := by
  unfold compiledNormalizedRoutedVariablePairDescriptorBlock
  rw [routedVariablePairPredicateTruthValues_descriptorPairTokens]
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq
    3 normalizedRoutedVariablePairTruthDescriptorBlock _ (by simp)]
  rfl

@[simp] theorem
    compiledNormalizedRoutedVariablePairDescriptorStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    compiledNormalizedRoutedVariablePairDescriptorStream
        (encodeDescriptorPairs pairs) =
      pairs.flatMap normalizedRoutedVariablePairDescriptorBlock := by
  unfold compiledNormalizedRoutedVariablePairDescriptorStream
  rw [mappedOutput_encodeDescriptorPairs]
  apply List.flatMap_congr
  intro pair _pairMember
  exact
    compiledNormalizedRoutedVariablePairDescriptorBlock_descriptorPairTokens
      pair

@[simp] theorem
    compiledNormalizedRoutedVariablePairDescriptorStream_descriptorSquare
    (descriptors : List RouteDescriptor) :
    compiledNormalizedRoutedVariablePairDescriptorStream
        (encodeDescriptorPairs (descriptors ×ˢ descriptors)) =
      normalizedRoutedVariablePairDescriptorScan descriptors := by
  rw [compiledNormalizedRoutedVariablePairDescriptorStream_encodeDescriptorPairs]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
