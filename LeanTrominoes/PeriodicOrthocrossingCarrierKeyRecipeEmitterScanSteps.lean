/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Input-scan steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_scan_nil (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (inputEq : data.input = []) (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanCfg state data) =
      some (beginEmissionCfg recipes state { data with input := [] }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change input = [] at inputEq
  change payload = none at payloadEq
  subst input
  subst payload
  by_cases nonempty : 0 < recipes.length <;>
    simp [TM2.step, program, scanCfg, cfg, tapes, readInput,
      clearPayload, payloadPresent, beginEmission, beginEmissionCfg,
      nonempty, emitCfg, clearFirstRouteCfg]

theorem step_scan_firstRoute (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (tail : List CarrierKeyRecipeEmitter.Token)
    (inputEq : data.input = .routeUnit .first :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanCfg state data) =
      some (scanCfg state
        { data with
          input := tail
          firstRoute := () :: data.firstRoute }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change input = .routeUnit .first :: tail at inputEq
  change payload = none at payloadEq
  subst input
  subst payload
  simp [TM2.step, program, scanCfg, cfg, tapes, readInput,
    payloadPresent, isRouteUnit, clearPayload]

theorem step_scan_secondRoute (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData)
    (tail : List CarrierKeyRecipeEmitter.Token)
    (inputEq : data.input = .routeUnit .second :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanCfg state data) =
      some (scanCfg state
        { data with
          input := tail
          secondRoute := () :: data.secondRoute }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change input = .routeUnit .second :: tail at inputEq
  change payload = none at payloadEq
  subst input
  subst payload
  simp [TM2.step, program, scanCfg, cfg, tapes, readInput,
    payloadPresent, isRouteUnit, clearPayload]

theorem step_scan_activation (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData) (active : Bool)
    (tail : List CarrierKeyRecipeEmitter.Token)
    (inputEq : data.input = .activation active :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (scanCfg state data) =
      some (scanCfg
        { actives := FixedLengthWordEvaluator.shiftAppend
            state.actives active
          payload := none }
        { data with input := tail }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change input = .activation active :: tail at inputEq
  change payload = none at payloadEq
  subst input
  subst payload
  simp [TM2.step, program, scanCfg, cfg, tapes, readInput,
    payloadPresent, isRouteUnit, isActivation, storeActivation,
    clearPayload]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
