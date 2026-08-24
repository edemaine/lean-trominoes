/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRecipeSuffixSemantics

/-! # Complete remaining-recipe execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipeSuffix_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData)
    (firstRouteEq : data.firstRoute = routeUnits input .first)
    (secondRouteEq : data.secondRoute = routeUnits input .second)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (emitCfg index state data)
      (some (clearFirstRouteCfg state
        { data with
          firstRoute := routeUnits input .first
          secondRoute := routeUnits input .second
          scratch := []
          outputReverse :=
            (recipeSuffixTokens recipes input state index).reverse ++
              data.outputReverse }))
      (recipeSuffixTime recipes input state index) := by
  have first := recipe_evalsInTime recipes input index state data
    firstRouteEq secondRouteEq scratchEq payloadEq
  by_cases nextExists : index.val + 1 < recipes.length
  · let nextIndex : Fin recipes.length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData :=
      { data with
        firstRoute := routeUnits input .first
        secondRoute := routeUnits input .second
        scratch := []
        outputReverse :=
          (tokenBlock input (state.actives.get index)
            (recipes.get index)).reverse ++ data.outputReverse }
    have first' : EvalsToInTime (TM2.step (program recipes))
        (emitCfg index state data) (some (emitCfg nextIndex state currentData))
        (recipeTime input (state.actives.get index)
          (recipes.get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := recipeSuffix_evalsInTime recipes input nextIndex state
      currentData rfl rfl rfl payloadEq
    have composed := EvalsToInTime.trans
      (TM2.step (program recipes))
      (recipeTime input (state.actives.get index) (recipes.get index))
      (recipeSuffixTime recipes input state nextIndex)
      (emitCfg index state data) (emitCfg nextIndex state currentData)
      (some (clearFirstRouteCfg state
        { currentData with
          firstRoute := routeUnits input .first
          secondRoute := routeUnits input .second
          scratch := []
          outputReverse :=
            (recipeSuffixTokens recipes input state nextIndex).reverse ++
              currentData.outputReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, nextIndex, currentData, List.reverse_append,
        List.append_assoc]
    · rw [recipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime (TM2.step (program recipes))
        (emitCfg index state data)
        (some (clearFirstRouteCfg state
          { data with
            firstRoute := routeUnits input .first
            secondRoute := routeUnits input .second
            scratch := []
            outputReverse :=
              (tokenBlock input (state.actives.get index)
                (recipes.get index)).reverse ++ data.outputReverse }))
        (recipeTime input (state.actives.get index)
          (recipes.get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [recipeSuffixTime_eq]
      simp [nextExists]
termination_by recipes.length - index.val
decreasing_by omega

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
