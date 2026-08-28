/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordSelection
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordCleanupSemantics
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of exact routed-variable compact atom-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordStream

def compactWords (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    RouteDescriptorPairAffine.routedVariableCompactAtomWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.routedVariableCompactAtomWords tokens⟩ := by
  unfold emittedTokens
  rw [RoutedVariableCompactAtomWordEmitter.emittedTokens_eq_encode,
    RoutedVariableCompactAtomWordCleanup.tokens_encode]
  rfl

@[simp] theorem emittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨compactWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [emittedTokens_eq_encode]
  unfold compactWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

/-- If every inner descriptor has one of the finite local route shapes, the
physical stream encodes the route-shape-independent pair scan. -/
theorem emittedStream_encodeDescriptorPairs_eq_pairBlocks
    (pairs : List (RouteDescriptor × RouteDescriptor))
    (hasLocalShape : ∀ pair ∈ pairs,
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape pair.2) :
    emittedStream (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode
        ⟨pairs.flatMap
          RouteDescriptorPairAffine.routedVariableCompactAtomWordPairBlock⟩ := by
  rw [emittedStream_encodeDescriptorPairs]
  congr 1
  congr 1
  unfold compactWords
  apply List.flatMap_congr
  intro pair pairMember
  exact RouteDescriptorPairAffine.routedVariableCompactAtomWords_descriptorPairTokens pair
      (hasLocalShape pair pairMember)

end RoutedVariableCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing
