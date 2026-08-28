/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyCandidateSemantics
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairMatchSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidatePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairMatchStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairSemantics

/-! # Semantics of common-shift canonical-left source-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateWords
open PaddedSupportedCandidateBlocks
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlocks_canonicalCrossingShiftLeftSourceKeyRecipePairBlocks :
    componentRecipeBlocks canonicalCrossingShiftLeftSourceKeyRecipePairBlocks =
      canonicalCrossingShiftLeftSourceKeyRecipeBlocks := by
  unfold componentRecipeBlocks
    canonicalCrossingShiftLeftSourceKeyRecipePairBlocks
    canonicalCrossingShiftLeftSourceKeyRecipeBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _slotMember
  simp [componentRecipeBlock,
    occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock,
    occurrencePairCanonicalCrossingLeftSourceKeyRecipeBlock]

theorem canonicalCrossingShiftLeftSourceKeyRecipePairBlocks_matchNode
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair)))
      canonicalCrossingShiftLeftSourceKeyRecipePairBlocks
      (canonicalCrossingShiftLeftCarrierNodeTemplateBlocks pair) := by
  unfold canonicalCrossingShiftLeftSourceKeyRecipePairBlocks
    canonicalCrossingShiftLeftCarrierNodeTemplateBlocks
  induction canonicalCrossingShiftSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      exact List.Forall₂.cons
        (slot.canonicalLeftSourceKeyRecipePairBlock_matchesNode pair)
        induction

theorem canonicalCrossingShiftLeftSourceKeyRecipePairWords_eq_candidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        (descriptorTokens (descriptorSlotPairTokens pair))
        (canonicalCrossingShiftSlots.map fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair))
        canonicalCrossingShiftLeftSourceKeyRecipePairBlocks =
      (canonicalCrossingShiftLeftCarrierNodeCandidates pair).map
        CarrierNodeSourceKeyCandidateWords.componentPair := by
  unfold canonicalCrossingShiftLeftCarrierNodeCandidates
  apply words_eq_map_componentPair_candidates
  rw [descriptorTokens_descriptorSlotPairTokens]
  exact canonicalCrossingShiftLeftSourceKeyRecipePairBlocks_matchNode
    (pair.1.1, pair.2.1)

theorem componentWords_canonicalCrossingShiftLeftCarrierNodeCandidates
    (pair : TaggedDescriptor × TaggedDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (canonicalCrossingShiftLeftCarrierNodeCandidates pair)) =
      ⟨canonicalCrossingShiftLeftSourceKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [← canonicalCrossingShiftLeftSourceKeyRecipePairWords_eq_candidates,
    componentWords_words,
    componentRecipeBlocks_canonicalCrossingShiftLeftSourceKeyRecipePairBlocks]
  rfl

/-- Merging the shifted component words gives the guarded compact source-key
candidate list. -/
theorem mergeWords_canonicalCrossingShiftLeftSourceKeyGuardedWords
    (pair : TaggedDescriptor × TaggedDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.mergeWords
        (canonicalCrossingShiftLeftSourceKeyGuardedWords
          (descriptorSlotPairTokens pair)) =
      (canonicalCrossingShiftLeftSourceKeyCandidates pair).map
        (guardedWord CarrierNodeSourceKeys.word) := by
  have components :=
    componentWords_canonicalCrossingShiftLeftCarrierNodeCandidates pair
  have merged := congrArg DelimitedBinaryWordGuardedPairMerge.mergeWords
    (congrArg DelimitedBinaryWords.Input.words components)
  rw [DelimitedBinaryWordGuardedPairMerge.mergeWords_componentWords] at merged
  unfold DelimitedBinaryWordGuardedPairMerge.mergedWords at merged
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs at merged
  unfold canonicalCrossingShiftLeftSourceKeyCandidates at ⊢
  simpa only [List.map_map, Function.comp_def,
    CarrierNodeSourceKeyCandidateWords.mergePair_componentPair]
    using merged.symm

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
