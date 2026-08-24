/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordPairCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyGuardedWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeStreamSemantics

/-! # Semantics of the complete carrier-key candidate-word stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

open PaddedSupportedCandidateWords
open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  TerminalCarrierKeyRecipeStream.guardedWords
      (descriptors ×ˢ descriptors) ++
    CrossingCarrierKeyRecipeStream.guardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

@[simp] theorem terminalTags_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorPairFieldTags.encodeDescriptorPairs
        (descriptors ×ˢ descriptors) := by
  unfold terminalTags
  rw [RouteDescriptorBinaryWordPairs.pairProduct_words_eq_descriptorWordPairs,
    RouteDescriptorPairFieldTags.inputTokens_descriptorWordPairs]

@[simp] theorem crossingTags_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTags (RouteDescriptorBinaryWords.words descriptors) =
      RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors) := by
  unfold crossingTags
  rw [expandedPairs_descriptorWords,
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens_wordPairs]

@[simp] theorem terminalTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨TerminalCarrierKeyRecipeStream.guardedWords
          (descriptors ×ˢ descriptors)⟩ := by
  unfold terminalTokens
  rw [terminalTags_descriptorWords,
    TerminalCarrierKeyRecipeStream.emittedStream_encodeDescriptorPairs]

@[simp] theorem crossingTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    crossingTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨CrossingCarrierKeyRecipeStream.guardedWords
          (taggedDescriptors descriptors ×ˢ
            taggedDescriptors descriptors)⟩ := by
  unfold crossingTokens
  rw [crossingTags_descriptorWords,
    CrossingCarrierKeyRecipeStream.emittedStream_encodeDescriptorSlotPairs]

/-- On canonical descriptor words, the combined compiler emits the exact
terminal-prefix/crossing-suffix guarded-word stream. -/
@[simp] theorem emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedWords descriptors⟩ := by
  rw [emittedTokens, terminalTokens_descriptorWords,
    crossingTokens_descriptorWords]
  simp [guardedWords, DelimitedBinaryWords.encode,
    List.flatMap_append]

/-- The combined guarded words are exactly the word representation of the
existing complete padded candidate stream. -/
theorem guardedWords_eq_paddedCandidateStream
    (descriptors : List RouteDescriptor) :
    guardedWords descriptors =
      (paddedCarrierKeyCandidateStream descriptors).map
        (guardedWord CarrierKeyWords.word) := by
  unfold guardedWords TerminalCarrierKeyRecipeStream.guardedWords
    CrossingCarrierKeyRecipeStream.guardedWords
    paddedCarrierKeyCandidateStream
    RouteDescriptorPairAffine.paddedTerminalCarrierKeyCandidateStream
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierKeyCandidateStream
  rw [List.map_append, List.map_flatMap, List.map_flatMap]
  apply congrArg₂ (fun first second => first ++ second)
  · apply List.flatMap_congr
    intro pair _
    exact RouteDescriptorPairAffine.terminalCarrierKeyGuardedWords_descriptorPairTokens
      pair
  · apply List.flatMap_congr
    intro pair _
    exact RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords_descriptorSlotPairTokens
      pair

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing
