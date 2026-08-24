/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterEmitSteps
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRouteRestoreExecution
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRouteScanExecution
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanData

/-! # Active first-side carrier-key recipe execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def activeFirst_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) (sideEq : (recipes.get index).side = .first)
    (activeEq : activeAt recipes state index = true)
    (routeEq : data.firstRoute = routeUnits input .first)
    (scratchEq : data.scratch = [])
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (emitCfg index state data)
      (some (afterRecipeCfg recipes index state
        { data with
          firstRoute := routeUnits input .first
          scratch := []
          outputReverse :=
            (activeTokens input (recipes.get index)).reverse ++
              data.outputReverse }))
      (2 * (routeUnits input .first).length + 3) := by
  let word := routeUnits input .first
  let prefixData : TapeData :=
    { data with
      outputReverse := activePrefixTokens.reverse ++ data.outputReverse }
  have first := oneStep
    (step_emit_active recipes index state data activeEq)
  have scanned := scanRouteFirst_evalsInTime recipes index sideEq word state
    prefixData (by simpa [word, prefixData] using routeEq) payloadEq
  let scannedData : TapeData :=
    { prefixData with
      firstRoute := []
      scratch := word.reverse
      outputReverse := List.replicate word.length (.bit false) ++
        prefixData.outputReverse }
  have firstTwo := EvalsToInTime.trans
    (TM2.step (program recipes)) 1 (word.length + 1)
    (emitCfg index state data) (scanRouteCfg index state prefixData)
    (some (restoreRouteCfg index state scannedData)) first (by
      simpa [scannedData, prefixData, scratchEq] using scanned)
  have restored := restoreRouteFirst_evalsInTime recipes index sideEq
    word.reverse state scannedData rfl payloadEq
  have whole := EvalsToInTime.trans
    (TM2.step (program recipes)) (word.length + 2) (word.length + 1)
    (emitCfg index state data) (restoreRouteCfg index state scannedData)
    (some (afterRecipeCfg recipes index state
      { data with
        firstRoute := word
        scratch := []
        outputReverse :=
          (activeTokens input (recipes.get index)).reverse ++
            data.outputReverse }))
    firstTwo (by
      convert restored using 1
      · unfold activeTokens
        rw [sideEq]
        simp [scannedData, prefixData, word, routeUnits,
          List.reverse_append, List.append_assoc]
      · simp)
  have timeEq : 2 * (routeUnits input .first).length + 3 =
      word.length + 1 + (word.length + 2) := by
    dsimp [word]
    omega
  rw [timeEq]
  simpa [word] using whole

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
