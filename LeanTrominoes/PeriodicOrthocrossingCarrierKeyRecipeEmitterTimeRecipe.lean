/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecution

/-! # Per-recipe bounds for the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

namespace Recipe

/-- Fixed additive output bound for one carrier-key recipe. -/
def outputWeight (recipe : Recipe) : Nat :=
  activePrefixTokens.length + (activeSuffixTokens recipe).length +
    sentinelTokens.length

theorem tokenBlock_length_le
    (input : List CarrierKeyRecipeEmitter.Token)
    (active : Bool) (recipe : Recipe) :
    (tokenBlock input active recipe).length ≤
      input.length + outputWeight recipe := by
  have routeBound : CarrierKeyRecipeEmitter.routeCount input recipe.side ≤
      input.length := by
    exact List.count_le_length
  by_cases enabled : active && recipe.supported
  · simp [tokenBlock, enabled, activeTokens, outputWeight]
    omega
  · simp [tokenBlock, enabled, outputWeight]
    omega

theorem time_le (input : List CarrierKeyRecipeEmitter.Token)
    (active : Bool) (recipe : Recipe) :
    recipeTime input active recipe ≤ 2 * input.length + 3 := by
  have routeBound : CarrierKeyRecipeEmitter.routeCount input recipe.side ≤
      input.length := by
    exact List.count_le_length
  by_cases enabled : active && recipe.supported
  · simp [recipeTime, enabled]
    omega
  · simp [recipeTime, enabled]

end Recipe

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
