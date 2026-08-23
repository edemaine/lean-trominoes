/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairCompiledSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Exact semantics of the routed-variable descriptor-pair stream -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

@[simp] theorem compiledRoutedVariablePairDescriptorStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    compiledRoutedVariablePairDescriptorStream
        (encodeDescriptorPairs pairs) =
      pairs.flatMap routedVariablePairDescriptorBlock := by
  unfold compiledRoutedVariablePairDescriptorStream
  rw [mappedOutput_encodeDescriptorPairs]
  apply List.flatMap_congr
  intro pair _pairMember
  exact compiledRoutedVariablePairDescriptorBlock_descriptorPairTokens pair

/-- On a canonical row-major descriptor square, the compiled tagged stream
is exactly the semantic pair scan. -/
@[simp] theorem compiledRoutedVariablePairDescriptorStream_descriptorSquare
    (descriptors : List RouteDescriptor) :
    compiledRoutedVariablePairDescriptorStream
        (encodeDescriptorPairs (descriptors ×ˢ descriptors)) =
      routedVariablePairDescriptorScan descriptors := by
  rw [compiledRoutedVariablePairDescriptorStream_encodeDescriptorPairs]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
