/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterStepBasics

/-! # Recipe-dispatch steps of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem step_emit_active (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (activeEq : activeAt recipes state index = true) :
    TM2.step (program recipes) (emitCfg index state data) =
      some (scanRouteCfg index state
        { data with
          outputReverse := activePrefixTokens.reverse ++
            data.outputReverse }) := by
  simp only [TM2.step, program, emitCfg, scanRouteCfg, cfg]
  simp only [TM2.stepAux]
  simp only [activeEq, Bool.cond_true]
  rw [stepAux_pushTokens]
  rfl

theorem step_emit_inactive (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (activeEq : activeAt recipes state index = false) :
    TM2.step (program recipes) (emitCfg index state data) =
      some (afterRecipeCfg recipes index state
        { data with
          outputReverse := sentinelTokens.reverse ++
            data.outputReverse }) := by
  simp only [TM2.step, program, emitCfg, cfg]
  simp only [TM2.stepAux]
  simp only [activeEq, Bool.cond_false]
  rw [stepAux_pushTokens]
  by_cases nextExists : index.val + 1 < recipes.length <;>
    simp [afterRecipe, afterRecipeCfg, nextExists, emitCfg,
      clearFirstRouteCfg, cfg]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
