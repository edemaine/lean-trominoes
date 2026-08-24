/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterCleanupExecution
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterReverseExecution

/-! # Cleanup-and-reverse suffix of carrier-key recipe-emitter execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def cleanup_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    EvalsToInTime (TM2.step (program recipes))
      (clearFirstRouteCfg
        (scanState (initialState recipes.length) input)
        (emittedData recipes input))
      (some (haltDataCfg (initialState recipes.length)
        ⟨[], [], [], [], [], compiledTokens recipes input⟩))
      (cleanupTime input + (compiledTokens recipes input).length + 1) := by
  let state := scanState (initialState recipes.length) input
  have payloadEq : state.payload = none :=
    scanState_payload (initialState recipes.length) input rfl
  have clearRun := clearRoutes_evalsInTime recipes state
    (routeUnits input .first) (routeUnits input .second)
    (emittedData recipes input) rfl rfl payloadEq
  have reverseRun := reverseOutput_evalsInTime recipes state
    (compiledTokens recipes input).reverse (clearedData recipes input) rfl
    payloadEq
  have whole := EvalsToInTime.trans
    (TM2.step (program recipes)) (cleanupTime input)
    ((compiledTokens recipes input).length + 1)
    (clearFirstRouteCfg state (emittedData recipes input))
    (reverseOutputCfg state (clearedData recipes input))
    (some (haltDataCfg (initialState recipes.length)
      ⟨[], [], [], [], [], compiledTokens recipes input⟩))
    (by simpa [cleanupTime, clearedData] using clearRun)
    (by
      simpa [clearedData, emittedData, scannedData] using reverseRun)
  convert whole using 1
  omega

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
