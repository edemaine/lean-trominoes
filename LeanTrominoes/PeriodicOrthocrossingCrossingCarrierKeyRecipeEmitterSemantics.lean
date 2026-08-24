/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyGuardedWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Semantics of compiled crossing carrier-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingCarrierKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem expandedActives_length_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives
      (descriptorSlotPairTokens pair)).length = recipes.length := by
  rw [RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives_descriptorSlotPairTokens]
  unfold recipes
  exact expandedActives_length_of_length_eq _ _ (by
    simp [RouteDescriptorOccurrenceSlotCrossing.crossingActivations,
      RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyRecipeBlocks])

@[simp] theorem preparedInput_activationBits_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput (descriptorSlotPairTokens pair))).length =
        recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact expandedActives_length_descriptorSlotPairTokens pair

theorem output_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    CarrierKeyRecipeEmitter.output recipes
        (preparedInput (descriptorSlotPairTokens pair)) =
      ⟨RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives_descriptorSlotPairTokens]
  have wordsEq :
      flattenedWords
          (descriptorTokens (descriptorSlotPairTokens pair))
          (RouteDescriptorOccurrenceSlotCrossing.crossingActivations
            (descriptorSlotPairTokens pair))
          RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyRecipeBlocks =
        RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords
          (descriptorSlotPairTokens pair) := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg (fun words => DelimitedBinaryWords.Input.mk words) wordsEq

/-- The compiled physical stream on a canonical slot pair is exactly the
delimiter encoding of its semantic crossing guarded-word block. -/
@[simp] theorem emittedTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyGuardedWords
          (descriptorSlotPairTokens pair)⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput (descriptorSlotPairTokens pair))
      (preparedInput_activationBits_descriptorSlotPairTokens pair),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_descriptorSlotPairTokens]

end CrossingCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
