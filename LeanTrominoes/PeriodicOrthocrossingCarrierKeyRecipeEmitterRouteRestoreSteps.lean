/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Route-counter restore steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_restoreRoute_first_nil (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .first)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (restoreRouteCfg index state data) =
      some (afterRecipeCfg recipes index state
        { data with
          scratch := []
          outputReverse :=
            (activeSuffixTokens (recipes.get index)).reverse ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change scratch = [] at scratchEq
  change payload = none at payloadEq
  subst scratch
  subst payload
  simp only [TM2.step, program, restoreRouteCfg, cfg]
  rw [sideEq]
  simp only [TM2.stepAux, tapes, List.head?_nil, List.tail_nil,
    readUnit, clearPayload, payloadPresent, Option.isSome,
    Bool.cond_false, update_tapes_scratch]
  rw [stepAux_pushTokens]
  by_cases nextExists : index.val + 1 < recipes.length <;>
    simp [afterRecipe, afterRecipeCfg, nextExists, emitCfg,
      clearFirstRouteCfg, cfg]

theorem step_restoreRoute_first_cons (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .first)
    (tail : List Unit) (scratchEq : data.scratch = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (restoreRouteCfg index state data) =
      some (restoreRouteCfg index state
        { data with
          firstRoute := () :: data.firstRoute
          scratch := tail }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change scratch = () :: tail at scratchEq
  change payload = none at payloadEq
  subst scratch
  subst payload
  simp only [TM2.step, program, restoreRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

theorem step_restoreRoute_second_nil (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .second)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (restoreRouteCfg index state data) =
      some (afterRecipeCfg recipes index state
        { data with
          scratch := []
          outputReverse :=
            (activeSuffixTokens (recipes.get index)).reverse ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change scratch = [] at scratchEq
  change payload = none at payloadEq
  subst scratch
  subst payload
  simp only [TM2.step, program, restoreRouteCfg, cfg]
  rw [sideEq]
  simp only [TM2.stepAux, tapes, List.head?_nil, List.tail_nil,
    readUnit, clearPayload, payloadPresent, Option.isSome,
    Bool.cond_false, update_tapes_scratch]
  rw [stepAux_pushTokens]
  by_cases nextExists : index.val + 1 < recipes.length <;>
    simp [afterRecipe, afterRecipeCfg, nextExists, emitCfg,
      clearFirstRouteCfg, cfg]

theorem step_restoreRoute_second_cons (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .second)
    (tail : List Unit) (scratchEq : data.scratch = () :: tail)
    (payloadEq : state.payload = none) :
    TM2.step (program recipes) (restoreRouteCfg index state data) =
      some (restoreRouteCfg index state
        { data with
          secondRoute := () :: data.secondRoute
          scratch := tail }) := by
  rcases data with
    ⟨input, firstRoute, secondRoute, scratch, outputReverse, output⟩
  rcases state with ⟨actives, payload⟩
  change scratch = () :: tail at scratchEq
  change payload = none at payloadEq
  subst scratch
  subst payload
  simp only [TM2.step, program, restoreRouteCfg, cfg]
  rw [sideEq]
  simp [TM2.stepAux, tapes, readUnit, clearPayload, payloadPresent]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
