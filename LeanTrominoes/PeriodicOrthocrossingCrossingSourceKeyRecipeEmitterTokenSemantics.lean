/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterOutputSemantics

/-! # Physical output of crossing source-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingSourceKeyRecipeEmitter

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- The compiled physical stream on a canonical slot pair is exactly the
delimiter encoding of its semantic crossing source-key guarded words. -/
@[simp] theorem emittedTokens_descriptorSlotPairTokens
    (pair : TaggedDescriptor × TaggedDescriptor) :
    emittedTokens (descriptorSlotPairTokens pair) =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyGuardedWords
          (descriptorSlotPairTokens pair)⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput (descriptorSlotPairTokens pair))
      (preparedInput_activationBits_descriptorSlotPairTokens pair),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_descriptorSlotPairTokens]

end CrossingSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
