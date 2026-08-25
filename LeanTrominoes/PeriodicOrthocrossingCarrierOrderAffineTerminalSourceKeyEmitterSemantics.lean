/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Semantics of direction-split terminal source-key components -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalSourceKeyEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem expandedActives_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (RouteDescriptorPairAffine.terminalDirectionalSourceKeyExpandedActives
      tokens).length = recipes.length := by
  rw [RouteDescriptorPairAffine.terminalDirectionalSourceKeyExpandedActives_eq]
  unfold recipes
  apply expandedActives_length_of_length_eq
  rw [List.length_map]
  exact RouteDescriptorPairAffine.terminalDirectionalSourceKeyRecipeBlocks_length.symm

@[simp] theorem preparedInput_activationBits
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput tokens)).length = recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact expandedActives_length tokens

theorem output_eq (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.output recipes (preparedInput tokens) =
      ⟨RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords
        tokens⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.terminalDirectionalSourceKeyExpandedActives_eq]
  have wordsEq :
      flattenedWords tokens
          (RouteDescriptorPairAffine.terminalDirectionalPredicates.map
            fun predicate => predicate.evalTokens tokens)
          RouteDescriptorPairAffine.terminalDirectionalSourceKeyRecipeBlocks =
        RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords
          tokens := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg DelimitedBinaryWords.Input.mk wordsEq

@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords
          tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens) (preparedInput_activationBits tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end TerminalDirectionalSourceKeyEmitter
end LeanTrominoes.PeriodicOrthocrossing
