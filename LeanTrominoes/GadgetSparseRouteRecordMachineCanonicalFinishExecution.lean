/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalRouteExecution
import LeanTrominoes.GadgetSparseRouteRecordMachineCopyExecution
import LeanTrominoes.GadgetSparseRouteRecordMachineCleanupExecution

/-! # Reversal and cleanup of a canonical route-record output -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction.RouteRasterRequest

/-- Machine data after reversing a canonical record word. -/
def canonicalAfterReverseData (request : Request) : TapeData :=
  { canonicalAfterRouteData request with
    outputReverse := []
    output := complementRecordBlock request }

/-- Canonical halted data with only the designated output tape populated. -/
def finalData (output : List OutputToken) : TapeData :=
  ⟨[], [], [], [], [], [], [], output⟩

/-- Exact allowance for reversal and terminal cleanup. -/
def canonicalFinishTime (request : Request) : Nat :=
  (complementRecordBlock request).length + 1 +
    cleanupTime (canonicalAfterReverseData request)

/-- Reversal and cleanup turn the accumulated reverse word into the exact
semantic output and empty every work tape. -/
def canonicalFinish_evalsInTime (request : Request) :
    EvalsToInTime (TM2.step program)
      (cfg .reverseOutput (inputState .routeEnd)
        (canonicalAfterRouteData request))
      (some (haltCfg (finalData (complementRecordBlock request))))
      (canonicalFinishTime request) := by
  have reversed := reverseOutput_evalsInTime (inputState .routeEnd)
    (complementRecordBlock request).reverse
    (canonicalAfterRouteData request) rfl
  have reversed' : EvalsToInTime (TM2.step program)
      (cfg .reverseOutput (inputState .routeEnd)
        (canonicalAfterRouteData request))
      (some (clearInputCfg none (canonicalAfterReverseData request)))
      ((complementRecordBlock request).length + 1) := by
    simpa [canonicalAfterReverseData, canonicalAfterRouteData,
      locationData] using reversed
  have cleaned := cleanup_evalsInTime none
    (canonicalAfterReverseData request)
  have cleaned' : EvalsToInTime (TM2.step program)
      (clearInputCfg none (canonicalAfterReverseData request))
      (some (haltCfg (finalData (complementRecordBlock request))))
      (cleanupTime (canonicalAfterReverseData request)) := by
    simpa [clearedData, finalData, canonicalAfterReverseData,
      canonicalAfterRouteData, locationData] using cleaned
  have whole := EvalsToInTime.trans (TM2.step program)
    ((complementRecordBlock request).length + 1)
    (cleanupTime (canonicalAfterReverseData request))
    (cfg .reverseOutput (inputState .routeEnd)
      (canonicalAfterRouteData request))
    (clearInputCfg none (canonicalAfterReverseData request))
    (some (haltCfg (finalData (complementRecordBlock request))))
    reversed' cleaned'
  simpa [canonicalFinishTime, Nat.add_comm] using whole

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
