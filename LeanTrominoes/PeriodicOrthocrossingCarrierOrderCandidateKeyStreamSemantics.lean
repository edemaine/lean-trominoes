/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalKeyStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeyStreamCompiler

/-! # Semantics of the carrier order-coordinate candidate-key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  TerminalDirectionalCarrierKeyStream.guardedWords
      (descriptors ×ˢ descriptors) ++
    CrossingCarrierKeyRecipeStream.guardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

@[simp] theorem terminalTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨TerminalDirectionalCarrierKeyStream.guardedWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalTokens
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    TerminalDirectionalCarrierKeyStream.emittedStream_encodeDescriptorPairs]

@[simp] theorem crossingTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CrossingCarrierKeyRecipeStream.guardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  exact CarrierKeyRecipeStream.crossingTokens_descriptorWords descriptors

@[simp] theorem emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [emittedTokens, terminalTokens_descriptorWords,
    crossingTokens_descriptorWords]
  simp [guardedWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

end CarrierOrderCandidateKeyStream
end LeanTrominoes.PeriodicOrthocrossing
