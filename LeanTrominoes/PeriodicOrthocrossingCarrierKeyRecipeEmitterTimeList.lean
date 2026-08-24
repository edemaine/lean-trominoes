/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTimeRecipe

/-! # Recipe-list bounds for the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Sum of the fixed additive output bounds in one recipe list. -/
def outputWeight (recipes : List Recipe) : Nat :=
  (recipes.map Recipe.outputWeight).sum

theorem blocks_length_le (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) (actives : List Bool) :
    (List.zipWith (tokenBlock input) actives recipes).flatten.length ≤
      recipes.length * input.length + outputWeight recipes := by
  induction recipes generalizing actives with
  | nil => simp [outputWeight]
  | cons recipe recipes induction =>
      cases actives with
      | nil => simp [outputWeight]
      | cons active actives =>
          simp only [List.zipWith_cons_cons, List.flatten_cons,
            List.length_append, List.length_cons]
          have current := Recipe.tokenBlock_length_le input active recipe
          have rest := induction actives
          unfold outputWeight at rest ⊢
          calc
            (tokenBlock input active recipe).length +
                  (List.zipWith (tokenBlock input) actives recipes).flatten.length
                ≤ (input.length + Recipe.outputWeight recipe) +
                  (recipes.length * input.length +
                    (List.map Recipe.outputWeight recipes).sum) :=
              Nat.add_le_add current rest
            _ = (recipes.length + 1) * input.length +
                  (Recipe.outputWeight recipe +
                    (List.map Recipe.outputWeight recipes).sum) := by
              ring

theorem recipeTimes_sum_le (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) (actives : List Bool) :
    (List.zipWith (recipeTime input) actives recipes).sum ≤
      recipes.length * (2 * input.length + 3) := by
  induction recipes generalizing actives with
  | nil => simp
  | cons recipe recipes induction =>
      cases actives with
      | nil => simp
      | cons active actives =>
          simp only [List.zipWith_cons_cons, List.sum_cons,
            List.length_cons]
          have current := Recipe.time_le input active recipe
          have rest := induction actives
          calc
            recipeTime input active recipe +
                  (List.zipWith (recipeTime input) actives recipes).sum ≤
                (2 * input.length + 3) +
                  recipes.length * (2 * input.length + 3) :=
              Nat.add_le_add current rest
            _ = (recipes.length + 1) * (2 * input.length + 3) := by
              ring

theorem compiledTokens_length_le (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    (compiledTokens recipes input).length ≤
      recipes.length * input.length + outputWeight recipes := by
  unfold compiledTokens allRecipeTokens recipeBlocks
  exact blocks_length_le recipes input _

theorem allRecipeTime_le (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) :
    allRecipeTime recipes input state ≤
      recipes.length * (2 * input.length + 3) := by
  unfold allRecipeTime recipeTimes
  exact recipeTimes_sum_le recipes input _

theorem routeUnits_length_le (input : List CarrierKeyRecipeEmitter.Token)
    (side : RouteDescriptorPairFieldTags.Side) :
    (routeUnits input side).length ≤ input.length := by
  have countBound : input.count (.routeUnit side) ≤ input.length :=
    List.count_le_length
  simpa [routeUnits, CarrierKeyRecipeEmitter.routeCount] using countBound

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
