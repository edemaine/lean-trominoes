/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedCrossingSourceKeyCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipePairComponentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedTerminalSourceKeyCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeSlotData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterOutputSemantics

/-! # Normalized recipe outputs as padded carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipes

open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

theorem terminalOutput_eq_componentWords_pairWords
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalOutput tokens =
      DelimitedBinaryWordGuardedPairMerge.componentWords
        (RouteDescriptorPairSourceKeyRecipePairs.words tokens
          (RouteDescriptorPairAffine.carrierSegmentPredicates.map fun predicate =>
            predicate.evalTokens tokens)
          CarrierNormalizedSourceKeyRecipePairs.terminalRecipePairBlocks) := by
  unfold terminalOutput TerminalSourceKeyRecipeEmitter.preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.terminalSourceKeyExpandedActives_eq,
    RouteDescriptorPairSourceKeyRecipePairs.componentWords_words]
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [RouteDescriptorPairCarrierKeyWordRecipes.words_eq_flattenedWords]
  unfold RouteDescriptorPairCarrierKeyWordRecipes.flattenedWords
  rw [CarrierNormalizedSourceKeyRecipePairs.terminalComponentRecipes,
    CarrierNormalizedSourceKeyRecipePairs.terminalExpandedActives]
  rfl

theorem crossingOutput_eq_componentWords_pairWords
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingOutput (descriptorSlotPairTokens pair) =
      DelimitedBinaryWordGuardedPairMerge.componentWords
        (RouteDescriptorPairSourceKeyRecipePairs.words
          (descriptorTokens (descriptorSlotPairTokens pair))
          (RouteDescriptorOccurrenceSlotCrossing.crossingActivations
            (descriptorSlotPairTokens pair))
          CarrierNormalizedSourceKeyRecipePairs.crossingRecipePairBlocks) := by
  unfold crossingOutput CrossingSourceKeyRecipeEmitter.preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyExpandedActives_descriptorSlotPairTokens,
    RouteDescriptorPairSourceKeyRecipePairs.componentWords_words]
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [RouteDescriptorPairCarrierKeyWordRecipes.words_eq_flattenedWords]
  unfold RouteDescriptorPairCarrierKeyWordRecipes.flattenedWords
  rw [CarrierNormalizedSourceKeyRecipePairs.crossingComponentRecipes,
    CarrierNormalizedSourceKeyRecipePairs.crossingExpandedActives]

theorem terminalOutput_descriptorPairTokens_eq_normalizedCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    terminalOutput (descriptorPairTokens pair) =
      DelimitedBinaryWordGuardedPairMerge.componentWords
        ((RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates
          pair).map fun candidate =>
            CarrierNodeSourceKeyCandidateWords.componentPair
              (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
                pair.1.gridSize candidate)) := by
  rw [terminalOutput_eq_componentWords_pairWords,
    CarrierNormalizedSourceKeyRecipePairs.words_eq_map_componentPair_normalizedCandidates
      (descriptorPairTokens pair) pair.1.gridSize
      (RouteDescriptorPairAffine.carrierSegmentPredicates.map fun predicate =>
        predicate.evalTokens (descriptorPairTokens pair))
      CarrierNormalizedSourceKeyRecipePairs.terminalRecipePairBlocks
      (RouteDescriptorPairAffine.terminalCarrierNodeTemplateBlocks pair)
      (CarrierNormalizedSourceKeyRecipePairs.terminalRecipePairBlocks_matchNodeAtPeriod
        pair.1.gridSize pair)]
  rfl

theorem crossingOutput_descriptorSlotPairTokens_eq_normalizedCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingOutput (descriptorSlotPairTokens pair) =
      DelimitedBinaryWordGuardedPairMerge.componentWords
        ((RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates
          pair).map fun candidate =>
            CarrierNodeSourceKeyCandidateWords.componentPair
              (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
                pair.1.1.gridSize candidate)) := by
  rw [crossingOutput_eq_componentWords_pairWords,
    CarrierNormalizedSourceKeyRecipePairs.crossingRecipePairWords_eq_normalizedCandidates]

end CarrierNormalizedSourceKeyRecipes
end LeanTrominoes.PeriodicOrthocrossing
