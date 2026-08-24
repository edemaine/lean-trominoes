/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionCleanup
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionInterface
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionPrefix

/-! # Exact execution of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open Computability StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def machine_outputsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    TM2OutputsInTime (machine recipes) input
      (some (compiledTokens recipes input)) (totalTime recipes input) := by
  have prefixRun := prefix_evalsInTime recipes input
  have cleanupRun := cleanup_evalsInTime recipes input
  have whole := EvalsToInTime.trans
    (TM2.step (program recipes)) (prefixTime recipes input)
    (cleanupTime input + (compiledTokens recipes input).length + 1)
    (scanCfg (initialState recipes.length) (initialData input))
    (clearFirstRouteCfg
      (scanState (initialState recipes.length) input)
      (emittedData recipes input))
    (some (haltDataCfg (initialState recipes.length)
      ⟨[], [], [], [], [], compiledTokens recipes input⟩))
    prefixRun cleanupRun
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program recipes)))^[whole.steps]
        (some (initList (machine recipes) input)) =
      some (haltList (machine recipes) (compiledTokens recipes input))
    rw [initList_eq_scanCfg, haltList_eq_haltDataCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime]
      omega)

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
