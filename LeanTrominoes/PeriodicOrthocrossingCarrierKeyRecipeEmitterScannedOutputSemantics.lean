/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterAllRecipeExecution
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTokenSemantics

/-! # Output semantics after compact-input scanning -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem allRecipeTokens_scanState
    (recipes : List Recipe) (input : List CarrierKeyRecipeEmitter.Token)
    (lengthEq : (CarrierKeyRecipeEmitter.activationBits input).length =
      recipes.length) :
    allRecipeTokens recipes input
        (scanState (initialState recipes.length) input) =
      emittedTokens recipes input := by
  unfold allRecipeTokens recipeBlocks emittedTokens
  rw [scanState_initial_actives _ lengthEq]

@[simp] theorem allRecipeTokens_scanState_prepared
    (recipes : List Recipe)
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (lengthEq : actives.length = recipes.length) :
    allRecipeTokens recipes
        (CarrierKeyRecipeEmitter.prepared tokens actives)
        (scanState (initialState recipes.length)
          (CarrierKeyRecipeEmitter.prepared tokens actives)) =
      (List.zipWith
        (fun active recipe => DelimitedBinaryWords.wordTokens
          (recipe.word tokens active)) actives recipes).flatten := by
  rw [allRecipeTokens_scanState]
  · rw [emittedTokens_eq_encode,
      CarrierKeyRecipeEmitter.output_prepared]
    unfold DelimitedBinaryWords.encode
    induction actives generalizing recipes with
    | nil => rfl
    | cons active actives induction =>
        cases recipes with
        | nil => rfl
        | cons recipe recipes =>
            simp only [List.zipWith_cons_cons, List.flatMap_cons,
              List.flatten_cons]
            rw [induction recipes (by simpa using lengthEq)]
  · rw [CarrierKeyRecipeEmitter.activationBits_prepared]
    exact lengthEq

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
