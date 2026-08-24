/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterActivationLength

/-! # Prepared-input length of crossing source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem preparedInput_activationBits_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput (descriptorSlotPairTokens pair))).length =
        recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact expandedActives_length_descriptorSlotPairTokens pair

end CrossingSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
