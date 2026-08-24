/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeLength
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyRecipeEmitterSemantics

/-! # Semantics of compiled activity-supported crossing key words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingActiveCarrierKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem preparedInput_activationBits_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput (descriptorSlotPairTokens pair))).length =
        recipes.length := by
  unfold preparedInput
  rw [CrossingCarrierKeyRecipeEmitter.preparedInput_activationBits_descriptorSlotPairTokens]
  unfold recipes CrossingCarrierKeyRecipeEmitter.recipes
  exact (forceSupportedBlocks_flatten_length
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyRecipeBlocks).symm

theorem output_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    CarrierKeyRecipeEmitter.output recipes
        (preparedInput (descriptorSlotPairTokens pair)) =
      ⟨RouteDescriptorOccurrenceSlotCrossing.crossingActiveCarrierKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold preparedInput CrossingCarrierKeyRecipeEmitter.preparedInput
    recipes
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives_descriptorSlotPairTokens]
  rw [← expandedActives_forceSupportedBlocks]
  unfold RouteDescriptorOccurrenceSlotCrossing.crossingActiveCarrierKeyGuardedWords
  rw [words_eq_flattenedWords]
  rfl

/-- The compiled physical stream on a canonical slot pair is exactly the
delimiter encoding of its activity-supported crossing key words. -/
@[simp] theorem emittedTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorOccurrenceSlotCrossing.crossingActiveCarrierKeyGuardedWords
          (descriptorSlotPairTokens pair)⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput (descriptorSlotPairTokens pair))
      (preparedInput_activationBits_descriptorSlotPairTokens pair),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_descriptorSlotPairTokens]

end CrossingActiveCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
