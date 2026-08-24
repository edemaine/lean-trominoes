/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyGuardedWordData
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterPreparedLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Semantic output of crossing source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

theorem output_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    CarrierKeyRecipeEmitter.output recipes
        (preparedInput (descriptorSlotPairTokens pair)) =
      ⟨RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyGuardedWords
        (descriptorSlotPairTokens pair)⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyExpandedActives_descriptorSlotPairTokens]
  have wordsEq :
      flattenedWords
          (descriptorTokens (descriptorSlotPairTokens pair))
          (RouteDescriptorOccurrenceSlotCrossing.crossingActivations
            (descriptorSlotPairTokens pair))
          RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyRecipeBlocks =
        RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyGuardedWords
          (descriptorSlotPairTokens pair) := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg (fun words => DelimitedBinaryWords.Input.mk words) wordsEq

end CrossingSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
