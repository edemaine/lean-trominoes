/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterPreparedLength
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterPreparedLength

/-! # Semantics of fixed normalized carrier source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipes

/-- Normalized terminal recipe emission is exactly its semantic delimited
word package on every tagged descriptor-pair block. -/
@[simp] theorem terminalEmittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalEmittedTokens tokens =
      DelimitedBinaryWords.encode (terminalOutput tokens) := by
  unfold terminalEmittedTokens terminalOutput
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens]
  · exact CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode
      terminalRecipes (TerminalSourceKeyRecipeEmitter.preparedInput tokens)
  · simpa using
      TerminalSourceKeyRecipeEmitter.preparedInput_activationBits tokens

/-- On canonical tagged slot pairs, normalized crossing recipe emission is
exactly its semantic delimited word package. -/
@[simp] theorem crossingEmittedTokens_eq_encode
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    crossingEmittedTokens
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair) =
      DelimitedBinaryWords.encode
        (crossingOutput
          (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
            pair)) := by
  unfold crossingEmittedTokens crossingOutput
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens]
  · exact CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode
      crossingRecipes
      (CrossingSourceKeyRecipeEmitter.preparedInput
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair))
  · simpa using
      CrossingSourceKeyRecipeEmitter.preparedInput_activationBits_descriptorSlotPairTokens
        pair

end CarrierNormalizedSourceKeyRecipes
end LeanTrominoes.PeriodicOrthocrossing
