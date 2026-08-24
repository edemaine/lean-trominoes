/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Route-stack cleanup steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_clearFirstRoute_nil (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (routeEq : data.firstRoute = []) (payloadEq : state.payload = none) :
    TM2.step (program recipes) (clearFirstRouteCfg state data) =
      some (clearSecondRouteCfg state { data with firstRoute := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change firstRoute = [] at routeEq
  change payload = none at payloadEq
  subst firstRoute
  subst payload
  simp [TM2.step, program, clearFirstRouteCfg, clearSecondRouteCfg,
    cfg, tapes, readUnit, clearPayload, payloadPresent]

theorem step_clearFirstRoute_cons (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData) (tail : List Unit)
    (routeEq : data.firstRoute = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (clearFirstRouteCfg state data) =
      some (clearFirstRouteCfg state
        { data with firstRoute := tail }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change firstRoute = () :: tail at routeEq
  change payload = none at payloadEq
  subst firstRoute
  subst payload
  simp [TM2.step, program, clearFirstRouteCfg, cfg, tapes,
    readUnit, clearPayload, payloadPresent]

theorem step_clearSecondRoute_nil (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (routeEq : data.secondRoute = []) (payloadEq : state.payload = none) :
    TM2.step (program recipes) (clearSecondRouteCfg state data) =
      some (reverseOutputCfg state { data with secondRoute := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change secondRoute = [] at routeEq
  change payload = none at payloadEq
  subst secondRoute
  subst payload
  simp [TM2.step, program, clearSecondRouteCfg, reverseOutputCfg,
    cfg, tapes, readUnit, clearPayload, payloadPresent]

theorem step_clearSecondRoute_cons (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData) (tail : List Unit)
    (routeEq : data.secondRoute = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (clearSecondRouteCfg state data) =
      some (clearSecondRouteCfg state
        { data with secondRoute := tail }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change secondRoute = () :: tail at routeEq
  change payload = none at payloadEq
  subst secondRoute
  subst payload
  simp [TM2.step, program, clearSecondRouteCfg, cfg, tapes,
    readUnit, clearPayload, payloadPresent]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
