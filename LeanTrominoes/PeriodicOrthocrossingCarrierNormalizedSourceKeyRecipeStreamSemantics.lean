/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics

/-! # Semantics of normalized carrier source-key recipe streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem terminalEmittedStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    terminalEmittedStream
        (RouteDescriptorPairFieldTags.encodeDescriptorPairs pairs) =
      DelimitedBinaryWords.encode ⟨terminalGuardedWords pairs⟩ := by
  unfold terminalEmittedStream
  rw [RouteDescriptorPairFieldTags.mappedOutput_encodeDescriptorPairs]
  simp only [CarrierNormalizedSourceKeyRecipes.terminalEmittedTokens_eq_encode]
  unfold terminalGuardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

@[simp] theorem crossingEmittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    crossingEmittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode ⟨crossingGuardedWords pairs⟩ := by
  unfold crossingEmittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [CarrierNormalizedSourceKeyRecipes.crossingEmittedTokens_eq_encode]
  unfold crossingGuardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end CarrierNormalizedSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
