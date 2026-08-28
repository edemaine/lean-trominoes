/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyComponentStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Normalized carrier source-key components as padded candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

def normalizedComponentPairAtPeriod
    (period : Nat)
    (candidate :
      PaddedSupportedLastRepresentativeEqualityRows.Candidate CarrierNode) :
    List Bool × List Bool :=
  CarrierNodeSourceKeyCandidateWords.componentPair
    (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
      period candidate)

theorem terminalComponentWords_paddedCandidateStream
    (period : Nat) (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        ((RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
          descriptors).map (normalizedComponentPairAtPeriod period)) =
      ⟨CarrierNormalizedSourceKeyRecipeStream.terminalGuardedWords
        (descriptors ×ˢ descriptors)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
    CarrierNormalizedSourceKeyRecipeStream.terminalGuardedWords
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair pairMember
  have pairEq := congrArg DelimitedBinaryWords.Input.words
    (CarrierNormalizedSourceKeyRecipes.terminalOutput_descriptorPairTokens_eq_normalizedCandidates
      pair)
  have firstMember : pair.1 ∈ descriptors :=
    (List.mem_product.mp pairMember).1
  rw [periodEq pair.1 firstMember] at pairEq
  change List.flatMap (fun words => [words.1, words.2])
      (List.map
        (fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
              period candidate))
        (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates pair)) =
    (CarrierNormalizedSourceKeyRecipes.terminalOutput
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).words
  exact pairEq.symm

theorem crossingComponentWords_paddedCandidateStream
    (period : Nat) (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        ((RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
          descriptors).map (normalizedComponentPairAtPeriod period)) =
      ⟨CarrierNormalizedSourceKeyRecipeStream.crossingGuardedWords
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
    CarrierNormalizedSourceKeyRecipeStream.crossingGuardedWords
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair pairMember
  have pairEq := congrArg DelimitedBinaryWords.Input.words
    (CarrierNormalizedSourceKeyRecipes.crossingOutput_descriptorSlotPairTokens_eq_normalizedCandidates
      pair)
  have firstTaggedMember : pair.1 ∈ taggedDescriptors descriptors :=
    (List.mem_product.mp pairMember).1
  have firstMember : pair.1.1 ∈ descriptors := by
    unfold taggedDescriptors at firstTaggedMember
    rcases List.mem_flatMap.mp firstTaggedMember with
      ⟨descriptor, descriptorMember, taggedMember⟩
    rcases List.mem_map.mp taggedMember with
      ⟨slot, _slotMember, taggedEq⟩
    exact taggedEq ▸ descriptorMember
  rw [periodEq pair.1.1 firstMember] at pairEq
  change List.flatMap (fun words => [words.1, words.2])
      (List.map
        (fun candidate =>
          CarrierNodeSourceKeyCandidateWords.componentPair
            (CarrierNormalizedSourceKeyRecipePairs.normalizeCandidateAtPeriod
              period candidate))
        (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates
          pair)) =
    (CarrierNormalizedSourceKeyRecipes.crossingOutput
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
        pair)).words
  exact pairEq.symm

theorem componentWords_paddedCarrierNodeCandidateStream
    (period : Nat) (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        ((paddedCarrierNodeCandidateStream descriptors).map
          (normalizedComponentPairAtPeriod period)) =
      ⟨guardedWords descriptors⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold paddedCarrierNodeCandidateStream guardedWords
  rw [List.map_append, List.flatMap_append]
  exact congrArg₂ (fun first second => first ++ second)
    (congrArg DelimitedBinaryWords.Input.words
      (terminalComponentWords_paddedCandidateStream
        period descriptors periodEq))
    (congrArg DelimitedBinaryWords.Input.words
      (crossingComponentWords_paddedCandidateStream
        period descriptors periodEq))

theorem tokens_descriptorWords_eq_normalizedCandidateComponentWords
    (period : Nat) (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          ((paddedCarrierNodeCandidateStream descriptors).map
            (normalizedComponentPairAtPeriod period))) := by
  rw [tokens_descriptorWords,
    componentWords_paddedCarrierNodeCandidateStream
      period descriptors periodEq]

end CarrierNormalizedSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
