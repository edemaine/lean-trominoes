/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamSemantics

/-! # Semantics of carrier order-coordinate source-identity keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords

def componentWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  TerminalDirectionalSourceKeyStream.guardedComponentWords
      (descriptors ×ˢ descriptors) ++
    CrossingSourceKeyRecipeStream.guardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  DelimitedBinaryWordGuardedPairMerge.mergeWords
    (componentWords descriptors)

@[simp] theorem terminalComponentTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalComponentTokens
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨TerminalDirectionalSourceKeyStream.guardedComponentWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalComponentTokens
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    TerminalDirectionalSourceKeyStream.emittedStream_encodeDescriptorPairs]

@[simp] theorem crossingComponentTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingComponentTokens
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CrossingSourceKeyRecipeStream.guardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  unfold crossingComponentTokens
  rw [CarrierKeyRecipeStream.crossingTags_descriptorWords,
    CrossingSourceKeyRecipeStream.emittedStream_encodeDescriptorSlotPairs]

@[simp] theorem componentTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    componentTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨componentWords descriptors⟩ := by
  rw [componentTokens, terminalComponentTokens_descriptorWords,
    crossingComponentTokens_descriptorWords]
  simp [componentWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

@[simp] theorem emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [emittedTokens, componentTokens_descriptorWords,
    DelimitedBinaryWordGuardedPairMerge.tokens_encode_words]
  rfl

end CarrierOrderCandidateKeyStream
end LeanTrominoes.PeriodicOrthocrossing
