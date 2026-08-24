/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeStreamSemantics

/-! # Semantics of the complete activity-supported key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyRecipeStream

open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  TerminalActiveCarrierKeyRecipeStream.guardedWords
      (descriptors ×ˢ descriptors) ++
    CrossingActiveCarrierKeyRecipeStream.guardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

@[simp] theorem terminalTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨TerminalActiveCarrierKeyRecipeStream.guardedWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalTokens
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    TerminalActiveCarrierKeyRecipeStream.emittedStream_encodeDescriptorPairs]

@[simp] theorem crossingTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CrossingActiveCarrierKeyRecipeStream.guardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  unfold crossingTokens
  rw [CarrierKeyRecipeStream.crossingTags_descriptorWords,
    CrossingActiveCarrierKeyRecipeStream.emittedStream_encodeDescriptorSlotPairs]

/-- Canonical descriptor words emit the exact terminal-prefix/crossing-suffix
activity-supported carrier-key stream. -/
@[simp] theorem emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [emittedTokens, terminalTokens_descriptorWords,
    crossingTokens_descriptorWords]
  simp [guardedWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

end CarrierActiveKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
