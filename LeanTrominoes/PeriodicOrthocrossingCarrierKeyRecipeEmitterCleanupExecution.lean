/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterCleanupSteps

/-! # Complete route-stack cleanup of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def clearFirstRoute_evalsInTime (recipes : List Recipe)
    (state : State recipes.length) (word : List Unit) (data : TapeData)
    (routeEq : data.firstRoute = word) (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (clearFirstRouteCfg state data)
      (some (clearSecondRouteCfg state
        { data with firstRoute := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearFirstRoute_nil recipes state data routeEq payloadEq)
      simpa using step
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData := { data with firstRoute := word }
      have first := oneStep
        (step_clearFirstRoute_cons recipes state data word routeEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (clearFirstRouteCfg state data) (clearFirstRouteCfg state nextData)
        (some (clearSecondRouteCfg state
          { nextData with firstRoute := [] }))
        first rest
      simpa using composed

def clearSecondRoute_evalsInTime (recipes : List Recipe)
    (state : State recipes.length) (word : List Unit) (data : TapeData)
    (routeEq : data.secondRoute = word) (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (clearSecondRouteCfg state data)
      (some (reverseOutputCfg state
        { data with secondRoute := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearSecondRoute_nil recipes state data routeEq payloadEq)
      simpa using step
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData := { data with secondRoute := word }
      have first := oneStep
        (step_clearSecondRoute_cons recipes state data word routeEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (clearSecondRouteCfg state data)
        (clearSecondRouteCfg state nextData)
        (some (reverseOutputCfg state
          { nextData with secondRoute := [] }))
        first rest
      simpa using composed

def clearRoutes_evalsInTime (recipes : List Recipe)
    (state : State recipes.length) (first second : List Unit)
    (data : TapeData) (firstEq : data.firstRoute = first)
    (secondEq : data.secondRoute = second)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (clearFirstRouteCfg state data)
      (some (reverseOutputCfg state
        { data with
          firstRoute := []
          secondRoute := [] }))
      (first.length + second.length + 2) := by
  have clearedFirst := clearFirstRoute_evalsInTime recipes state first data
    firstEq payloadEq
  let firstData : TapeData := { data with firstRoute := [] }
  have clearedSecond := clearSecondRoute_evalsInTime recipes state second
    firstData (by simpa [firstData] using secondEq) payloadEq
  have whole := EvalsToInTime.trans
    (TM2.step (program recipes)) (first.length + 1) (second.length + 1)
    (clearFirstRouteCfg state data) (clearSecondRouteCfg state firstData)
    (some (reverseOutputCfg state
      { firstData with secondRoute := [] }))
    clearedFirst clearedSecond
  rw [show first.length + second.length + 2 =
    second.length + 1 + (first.length + 1) by omega]
  simpa [firstData] using whole

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
