/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyComponentStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCrossingTagSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyTerminalTagSemantics

/-! # Semantics of the complete normalized carrier source-key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

@[simp] theorem terminalTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CarrierNormalizedSourceKeyRecipeStream.terminalGuardedWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalTokens
  rw [CarrierSourceKeyComponentStream.terminalTags_descriptorWords,
    CarrierNormalizedSourceKeyRecipeStream.terminalEmittedStream_encodeDescriptorPairs]

@[simp] theorem crossingTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CarrierNormalizedSourceKeyRecipeStream.crossingGuardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  unfold crossingTokens
  rw [CarrierSourceKeyComponentStream.crossingTags_descriptorWords,
    CarrierNormalizedSourceKeyRecipeStream.crossingEmittedStream_encodeDescriptorSlotPairs]

@[simp] theorem tokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [tokens, terminalTokens_descriptorWords,
    crossingTokens_descriptorWords]
  simp [guardedWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

end CarrierNormalizedSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
