/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRouteRestoreSteps

/-! # Complete route-counter restores of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def restoreRouteFirst_evalsInTime (recipes : List Recipe)
    (index : Fin recipes.length)
    (sideEq : (recipes.get index).side = .first)
    (word : List Unit) (state : State recipes.length) (data : TapeData)
    (scratchEq : data.scratch = word)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (restoreRouteCfg index state data)
      (some (afterRecipeCfg recipes index state
        { data with
          firstRoute := word.reverse ++ data.firstRoute
          scratch := []
          outputReverse :=
            (activeSuffixTokens (recipes.get index)).reverse ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreRoute_first_nil recipes index state data sideEq
          scratchEq payloadEq)
      convert step using 1 <;> simp
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData :=
        { data with
          firstRoute := () :: data.firstRoute
          scratch := word }
      have first := oneStep
        (step_restoreRoute_first_cons recipes index state data sideEq word
          scratchEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (restoreRouteCfg index state data)
        (restoreRouteCfg index state nextData)
        (some (afterRecipeCfg recipes index state
          { nextData with
            firstRoute := word.reverse ++ nextData.firstRoute
            scratch := []
            outputReverse :=
              (activeSuffixTokens (recipes.get index)).reverse ++
                nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def restoreRouteSecond_evalsInTime (recipes : List Recipe)
    (index : Fin recipes.length)
    (sideEq : (recipes.get index).side = .second)
    (word : List Unit) (state : State recipes.length) (data : TapeData)
    (scratchEq : data.scratch = word)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (restoreRouteCfg index state data)
      (some (afterRecipeCfg recipes index state
        { data with
          secondRoute := word.reverse ++ data.secondRoute
          scratch := []
          outputReverse :=
            (activeSuffixTokens (recipes.get index)).reverse ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreRoute_second_nil recipes index state data sideEq
          scratchEq payloadEq)
      convert step using 1 <;> simp
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData :=
        { data with
          secondRoute := () :: data.secondRoute
          scratch := word }
      have first := oneStep
        (step_restoreRoute_second_cons recipes index state data sideEq word
          scratchEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (restoreRouteCfg index state data)
        (restoreRouteCfg index state nextData)
        (some (afterRecipeCfg recipes index state
          { nextData with
            secondRoute := word.reverse ++ nextData.secondRoute
            scratch := []
            outputReverse :=
              (activeSuffixTokens (recipes.get index)).reverse ++
                nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
