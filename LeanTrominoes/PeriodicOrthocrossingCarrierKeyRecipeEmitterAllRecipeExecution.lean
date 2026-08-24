/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRecipeSuffixExecution

/-! # Complete fixed recipe-list execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def allRecipeTokens (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) : List DelimitedBinaryWords.Token :=
  (recipeBlocks recipes input state).flatten

def allRecipeTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) : Nat :=
  (recipeTimes recipes input state).sum

@[simp] theorem recipeSuffixTokens_zero (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (nonempty : 0 < recipes.length) :
    recipeSuffixTokens recipes input state ⟨0, nonempty⟩ =
      allRecipeTokens recipes input state := by
  simp [recipeSuffixTokens, allRecipeTokens]

@[simp] theorem recipeSuffixTime_zero (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (nonempty : 0 < recipes.length) :
    recipeSuffixTime recipes input state ⟨0, nonempty⟩ =
      allRecipeTime recipes input state := by
  simp [recipeSuffixTime, allRecipeTime]

def allRecipes_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (data : TapeData)
    (firstRouteEq : data.firstRoute = routeUnits input .first)
    (secondRouteEq : data.secondRoute = routeUnits input .second)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (beginEmissionCfg recipes state data)
      (some (clearFirstRouteCfg state
        { data with
          firstRoute := routeUnits input .first
          secondRoute := routeUnits input .second
          scratch := []
          outputReverse :=
            (allRecipeTokens recipes input state).reverse ++
              data.outputReverse }))
      (allRecipeTime recipes input state) := by
  by_cases nonempty : 0 < recipes.length
  · have run := recipeSuffix_evalsInTime recipes input ⟨0, nonempty⟩
      state data firstRouteEq secondRouteEq scratchEq payloadEq
    simpa [beginEmissionCfg, nonempty] using run
  · cases recipes with
    | cons recipe recipes => simp at nonempty
    | nil =>
        have normalized :
            { data with
              firstRoute := routeUnits input .first
              secondRoute := routeUnits input .second
              scratch := [] } = data := by
          rcases data with
            ⟨source, firstRoute, secondRoute, scratch,
              outputReverse, output⟩
          simp_all
        have run := EvalsToInTime.refl (TM2.step (program []))
          (clearFirstRouteCfg state data)
        simpa [beginEmissionCfg, allRecipeTokens, recipeBlocks,
          allRecipeTime, recipeTimes, normalized] using run

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
