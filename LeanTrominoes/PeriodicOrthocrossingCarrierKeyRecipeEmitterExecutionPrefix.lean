/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanExecution

/-! # Scan-and-emit prefix of carrier-key recipe-emitter execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def prefix_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    EvalsToInTime (TM2.step (program recipes))
      (scanCfg (initialState recipes.length) (initialData input))
      (some (clearFirstRouteCfg
        (scanState (initialState recipes.length) input)
        (emittedData recipes input)))
      (prefixTime recipes input) := by
  let state := scanState (initialState recipes.length) input
  have scanRun := scan_evalsInTime recipes input
    (initialState recipes.length) (initialData input) rfl rfl
  have emitRun := allRecipes_evalsInTime recipes input state
    (scannedData input) rfl rfl rfl
    (scanState_payload (initialState recipes.length) input rfl)
  have whole := EvalsToInTime.trans
    (TM2.step (program recipes)) (input.length + 1)
    (allRecipeTime recipes input state)
    (scanCfg (initialState recipes.length) (initialData input))
    (beginEmissionCfg recipes state (scannedData input))
    (some (clearFirstRouteCfg state (emittedData recipes input)))
    (by simpa [state, initialData, scannedData] using scanRun)
    (by simpa [state, emittedData, compiledTokens, scannedData] using emitRun)
  simpa [prefixTime, state, Nat.add_comm] using whole

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
