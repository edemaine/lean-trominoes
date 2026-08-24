/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyActiveRecipeLength
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterSemantics

/-! # Semantics of compiled activity-supported terminal key words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalActiveCarrierKeyRecipeEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem preparedInput_activationBits
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (CarrierKeyRecipeEmitter.activationBits (preparedInput tokens)).length =
      recipes.length := by
  unfold preparedInput
  rw [TerminalCarrierKeyRecipeEmitter.preparedInput_activationBits]
  unfold recipes TerminalCarrierKeyRecipeEmitter.recipes
  exact (forceSupportedBlocks_flatten_length
    RouteDescriptorPairAffine.terminalCarrierKeyRecipeBlocks).symm

theorem output_eq (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.output recipes (preparedInput tokens) =
      ⟨RouteDescriptorPairAffine.terminalActiveCarrierKeyGuardedWords
        tokens⟩ := by
  unfold preparedInput TerminalCarrierKeyRecipeEmitter.preparedInput
    recipes
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives_eq]
  rw [← expandedActives_forceSupportedBlocks]
  unfold RouteDescriptorPairAffine.terminalActiveCarrierKeyGuardedWords
  rw [words_eq_flattenedWords]
  simp only [id_eq]
  rfl

/-- The compiled physical stream is exactly the delimiter encoding of the
activity-supported terminal carrier-key block. -/
@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.terminalActiveCarrierKeyGuardedWords
          tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens) (preparedInput_activationBits tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end TerminalActiveCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
