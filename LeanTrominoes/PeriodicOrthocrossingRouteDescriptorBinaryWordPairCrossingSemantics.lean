/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingData

/-! # Exact semantics of binary descriptor-pair crossing markers -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWordPairs

theorem product_map_map
    (firsts : List α) (seconds : List β)
    (firstMap : α → γ) (secondMap : β → δ) :
    (firsts.map firstMap ×ˢ seconds.map secondMap) =
      (firsts ×ˢ seconds).map fun pair =>
        (firstMap pair.1, secondMap pair.2) := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      simp only [List.map_cons, List.product_cons, List.map_append,
        List.map_map, Function.comp_def, induction]

/-- The generic ordered-word product of canonical descriptor words is exactly
the canonical descriptor-pair word list. -/
theorem pairProduct_words_eq_descriptorWordPairs
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordPairProductMachine.pairs
        (RouteDescriptorBinaryWords.words descriptors) =
      descriptorWordPairs descriptors := by
  unfold DelimitedBinaryWordPairProductMachine.pairs
    RouteDescriptorBinaryWords.words descriptorWordPairs
  exact congrArg DelimitedBinaryWordPairs.Input.mk
    (product_map_map descriptors descriptors
      RouteDescriptorBinaryWords.descriptorWord
      RouteDescriptorBinaryWords.descriptorWord)

@[simp] theorem wordPairCrossingMarkers_descriptorWords
    (marker : α) (first second : RouteDescriptor) :
    wordPairCrossingMarkers marker
        (RouteDescriptorBinaryWords.descriptorWord first,
          RouteDescriptorBinaryWords.descriptorWord second) =
      routeDescriptorPairCrossingMarkers marker (first, second) := by
  simp [wordPairCrossingMarkers]

/-- Interpreting canonical pair words recovers exactly the semantic
descriptor-pair marker blocks. -/
theorem crossingMarkers_descriptorWordPairs
    (marker : α) (descriptors : List RouteDescriptor) :
    crossingMarkers marker (descriptorWordPairs descriptors) =
      (routeDescriptorPairCrossingMarkerBlocks
        marker descriptors).flatten := by
  unfold crossingMarkers descriptorWordPairs
    routeDescriptorPairCrossingMarkerBlocks
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro pair pairMember
  exact wordPairCrossingMarkers_descriptorWords marker pair.1 pair.2

end RouteDescriptorBinaryWordPairs
end PeriodicOrthocrossing
end LeanTrominoes
