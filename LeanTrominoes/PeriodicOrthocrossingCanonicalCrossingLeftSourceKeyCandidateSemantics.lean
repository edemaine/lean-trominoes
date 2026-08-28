/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyCandidateData
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidatePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics

/-! # Semantics of canonical-left crossing source-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateWords
open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlocks_canonicalLeftSourceKeyRecipePairBlocks :
    componentRecipeBlocks canonicalLeftSourceKeyRecipePairBlocks =
      canonicalLeftSourceKeyRecipeBlocks := by
  unfold componentRecipeBlocks canonicalLeftSourceKeyRecipePairBlocks
    canonicalLeftSourceKeyRecipeBlocks
    Slot.canonicalLeftSourceKeyRecipePairBlock
    Slot.canonicalLeftSourceKeyRecipeBlock
    occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock
    occurrencePairCanonicalCrossingLeftSourceKeyRecipeBlock
  rw [List.map_map]
  rfl

theorem Slot.canonicalLeftSourceKeyRecipePairBlock_matchesNode
    (slot : Slot) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂ (MatchesNode
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair))
      slot.canonicalLeftSourceKeyRecipePairBlock
      (slot.canonicalLeftCarrierNodeTemplateBlock pair) := by
  unfold Slot.canonicalLeftSourceKeyRecipePairBlock
    occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock
    Slot.canonicalLeftCarrierNodeTemplateBlock
    Slot.canonicalCrossingRecord
  exact List.Forall₂.cons
    (occurrencePairCrossingSourceKeyRecipePair_matchesNode
      pair slot.occurrences (0, 0) .left true)
    List.Forall₂.nil

theorem canonicalLeftSourceKeyRecipePairBlocks_matchNode
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair)))
      canonicalLeftSourceKeyRecipePairBlocks
      (canonicalLeftCarrierNodeTemplateBlocks pair) := by
  unfold canonicalLeftSourceKeyRecipePairBlocks
    canonicalLeftCarrierNodeTemplateBlocks
  induction crossingSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      exact List.Forall₂.cons
        (slot.canonicalLeftSourceKeyRecipePairBlock_matchesNode pair)
        induction

theorem canonicalLeftSourceKeyRecipePairWords_eq_candidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorTokens (descriptorSlotPairTokens pair))
        (crossingActivations (descriptorSlotPairTokens pair))
        canonicalLeftSourceKeyRecipePairBlocks =
      (canonicalLeftCarrierNodeCandidates pair).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  unfold canonicalLeftCarrierNodeCandidates
  apply words_eq_map_componentPair_candidates
  rw [descriptorTokens_descriptorSlotPairTokens]
  exact canonicalLeftSourceKeyRecipePairBlocks_matchNode
    (pair.1.1, pair.2.1)

theorem componentWords_canonicalLeftCarrierNodeCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (canonicalLeftCarrierNodeCandidates pair)) =
      ⟨canonicalLeftSourceKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [← canonicalLeftSourceKeyRecipePairWords_eq_candidates,
    componentWords_words,
    componentRecipeBlocks_canonicalLeftSourceKeyRecipePairBlocks]
  rfl

/-- The complete merged output is the guarded-word presentation of the fixed
candidate list. -/
theorem mergeWords_canonicalLeftSourceKeyGuardedWords
    (pair : TaggedDescriptor × TaggedDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.mergeWords
        (canonicalLeftSourceKeyGuardedWords
          (descriptorSlotPairTokens pair)) =
      (canonicalLeftSourceKeyCandidates pair).map
        (guardedWord CarrierNodeSourceKeys.word) := by
  have components := componentWords_canonicalLeftCarrierNodeCandidates pair
  have merged := congrArg DelimitedBinaryWordGuardedPairMerge.mergeWords
    (congrArg DelimitedBinaryWords.Input.words components)
  rw [DelimitedBinaryWordGuardedPairMerge.mergeWords_componentWords] at merged
  unfold DelimitedBinaryWordGuardedPairMerge.mergedWords at merged
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs at merged
  unfold canonicalLeftSourceKeyCandidates at ⊢
  simpa only [List.map_map, Function.comp_def,
    CarrierNodeSourceKeyCandidateWords.mergePair_componentPair]
    using merged.symm

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
