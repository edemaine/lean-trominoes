/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Semantics of common-shift crossing source-key emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem preparedInput_activationBits_length
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput (descriptorSlotPairTokens pair))).length =
        recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyExpandedActives_length
    pair

theorem output_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    CarrierKeyRecipeEmitter.output recipes
        (preparedInput (descriptorSlotPairTokens pair)) =
      ⟨RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyExpandedActives_descriptorSlotPairTokens]
  have wordsEq :
      flattenedWords
          (descriptorTokens (descriptorSlotPairTokens pair))
          (RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftSlots.map
            fun slot => slot.evalTokens (descriptorSlotPairTokens pair))
          RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyRecipeBlocks =
        RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyGuardedWords
          (descriptorSlotPairTokens pair) := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg DelimitedBinaryWords.Input.mk wordsEq

@[simp] theorem emittedTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyGuardedWords
          (descriptorSlotPairTokens pair)⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput (descriptorSlotPairTokens pair))
      (preparedInput_activationBits_length pair),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_descriptorSlotPairTokens]

end CanonicalCrossingShiftLeftSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
