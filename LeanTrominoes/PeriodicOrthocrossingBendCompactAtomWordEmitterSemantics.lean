/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength

/-! # Semantics of guarded affine bend compact-word emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendCompactAtomWordEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem expandedActives_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (RouteDescriptorPairAffine.bendCompactAtomWordExpandedActives
      tokens).length = recipes.length := by
  rw [RouteDescriptorPairAffine.bendCompactAtomWordExpandedActives_eq]
  unfold recipes
  apply expandedActives_length_of_length_eq
  rw [List.length_map]
  exact RouteDescriptorPairAffine.bendCompactAtomWordRecipeBlocks_length.symm

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
      ⟨RouteDescriptorPairAffine.bendCompactAtomGuardedWords tokens⟩ := by
  unfold preparedInput recipes
  rw [CarrierKeyRecipeEmitter.preparedFrom_eq_prepared,
    CarrierKeyRecipeEmitter.output_prepared,
    RouteDescriptorPairAffine.bendCompactAtomWordExpandedActives_eq]
  have wordsEq :
      flattenedWords tokens
          (RouteDescriptorPairAffine.bendDescriptorPredicates.map
            fun predicate => predicate.evalTokens tokens)
          RouteDescriptorPairAffine.bendCompactAtomWordRecipeBlocks =
        RouteDescriptorPairAffine.bendCompactAtomGuardedWords tokens := by
    rw [← words_eq_flattenedWords]
    rfl
  exact congrArg DelimitedBinaryWords.Input.mk wordsEq

/-- The compiled physical stream is exactly the delimiter encoding of the
guarded affine bend recipe words. -/
@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.bendCompactAtomGuardedWords tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens) (preparedInput_activationBits tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end BendCompactAtomWordEmitter
end LeanTrominoes.PeriodicOrthocrossing
