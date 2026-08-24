/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Route-counter scan steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_scanRoute_first_nil (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .first)
    (routeEq : data.firstRoute = [])
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanRouteCfg index state data) =
      some (restoreRouteCfg index state
        { data with firstRoute := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change firstRoute = [] at routeEq
  change payload = none at payloadEq
  subst firstRoute
  subst payload
  simp only [TM2.step, program, scanRouteCfg, restoreRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

theorem step_scanRoute_first_cons (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .first)
    (tail : List Unit) (routeEq : data.firstRoute = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanRouteCfg index state data) =
      some (scanRouteCfg index state
        { data with
          firstRoute := tail
          scratch := () :: data.scratch
          outputReverse := .bit false :: data.outputReverse }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change firstRoute = () :: tail at routeEq
  change payload = none at payloadEq
  subst firstRoute
  subst payload
  simp only [TM2.step, program, scanRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

theorem step_scanRoute_second_nil (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .second)
    (routeEq : data.secondRoute = [])
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanRouteCfg index state data) =
      some (restoreRouteCfg index state
        { data with secondRoute := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change secondRoute = [] at routeEq
  change payload = none at payloadEq
  subst secondRoute
  subst payload
  simp only [TM2.step, program, scanRouteCfg, restoreRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

theorem step_scanRoute_second_cons (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .second)
    (tail : List Unit) (routeEq : data.secondRoute = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanRouteCfg index state data) =
      some (scanRouteCfg index state
        { data with
          secondRoute := tail
          scratch := () :: data.scratch
          outputReverse := .bit false :: data.outputReverse }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change secondRoute = () :: tail at routeEq
  change payload = none at payloadEq
  subst secondRoute
  subst payload
  simp only [TM2.step, program, scanRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
