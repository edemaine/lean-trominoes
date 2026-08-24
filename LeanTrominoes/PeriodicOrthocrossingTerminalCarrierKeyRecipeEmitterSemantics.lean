/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyGuardedWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterCompiler

/-! # Semantics of compiled terminal carrier-key guarded words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalCarrierKeyRecipeEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem expandedActives_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives tokens).length =
      recipes.length := by
  rw [RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives_eq]
  unfold recipes
  exact expandedActives_length_of_length_eq _ _
    (RouteDescriptorPairAffine.terminalCarrierKeyActivations_length tokens)

@[simp] theorem preparedInput_activationBits
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (CarrierKeyRecipeEmitter.activationBits (preparedInput tokens)).length =
      recipes.length := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.activationBits_prepared]
  exact expandedActives_length tokens

theorem output_eq (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.output recipes (preparedInput tokens) =
      ⟨RouteDescriptorPairAffine.terminalCarrierKeyGuardedWords tokens⟩ := by
  unfold preparedInput
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives_eq]
  have wordsEq :
      flattenedWords tokens
          (RouteDescriptorPairAffine.terminalCarrierKeyActivations tokens)
          RouteDescriptorPairAffine.terminalCarrierKeyRecipeBlocks =
        RouteDescriptorPairAffine.terminalCarrierKeyGuardedWords tokens := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg (fun words => DelimitedBinaryWords.Input.mk words) wordsEq

/-- The compiled physical stream is exactly the delimiter encoding of the
semantic terminal guarded-word block. -/
@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.terminalCarrierKeyGuardedWords tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens) (preparedInput_activationBits tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end TerminalCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
