/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterActiveFirstExecution
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterActiveSecondExecution

/-! # One complete carrier-key recipe execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipeTime (input : List CarrierKeyRecipeEmitter.Token)
    (active : Bool) (recipe : Recipe) : Nat :=
  if active && recipe.supported then
    2 * CarrierKeyRecipeEmitter.routeCount input recipe.side + 3
  else 1

def recipe_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData)
    (firstRouteEq : data.firstRoute = routeUnits input .first)
    (secondRouteEq : data.secondRoute = routeUnits input .second)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (emitCfg index state data)
      (some (afterRecipeCfg recipes index state
        { data with
          firstRoute := routeUnits input .first
          secondRoute := routeUnits input .second
          scratch := []
          outputReverse :=
            (tokenBlock input (state.actives.get index)
              (recipes.get index)).reverse ++ data.outputReverse }))
      (recipeTime input (state.actives.get index)
        (recipes.get index)) := by
  by_cases activeCase : activeAt recipes state index = true
  · have enabledEq :
        (state.actives.get index && (recipes.get index).supported) = true := by
      change (state.actives.get index &&
        (recipes.get index).supported) = true at activeCase
      exact activeCase
    have blockEq :
        tokenBlock input (state.actives.get index) (recipes.get index) =
          activeTokens input (recipes.get index) := by
      unfold tokenBlock
      rw [enabledEq]
      rfl
    have timeEq :
        recipeTime input (state.actives.get index) (recipes.get index) =
          2 * CarrierKeyRecipeEmitter.routeCount input
            (recipes.get index).side + 3 := by
      unfold recipeTime
      rw [enabledEq]
      rfl
    rw [blockEq, timeEq]
    cases sideEq : (recipes.get index).side with
    | first =>
        have run := activeFirst_evalsInTime recipes input index state data
          sideEq activeCase firstRouteEq scratchEq payloadEq
        simpa [routeUnits,
          firstRouteEq, secondRouteEq, scratchEq] using run
    | second =>
        have run := activeSecond_evalsInTime recipes input index state data
          sideEq activeCase secondRouteEq scratchEq payloadEq
        simpa [routeUnits,
          firstRouteEq, secondRouteEq, scratchEq] using run
  · have inactiveCase : activeAt recipes state index = false :=
      Bool.eq_false_of_not_eq_true activeCase
    have run := oneStep
      (step_emit_inactive recipes index state data inactiveCase)
    have disabledEq :
        (state.actives.get index && (recipes.get index).supported) = false := by
      change (state.actives.get index &&
        (recipes.get index).supported) = false at inactiveCase
      exact inactiveCase
    have blockEq :
        tokenBlock input (state.actives.get index) (recipes.get index) =
          sentinelTokens := by
      unfold tokenBlock
      rw [disabledEq]
      rfl
    have timeEq :
        recipeTime input (state.actives.get index) (recipes.get index) =
          1 := by
      unfold recipeTime
      rw [disabledEq]
      rfl
    rw [blockEq, timeEq]
    simpa [firstRouteEq, secondRouteEq, scratchEq] using run

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
