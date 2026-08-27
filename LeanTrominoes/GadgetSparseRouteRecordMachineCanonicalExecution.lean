/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalFinishExecution

/-! # Complete canonical execution of the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction.RouteRasterRequest

/-- Exact allowance for a valid canonical normalized request. -/
def canonicalTotalTime (request : Request) : Nat :=
  canonicalRouteTime request + canonicalFinishTime request

theorem initList_eq_initialCfg (tokens : List InputToken) :
    initList machine tokens = initialCfg tokens := by
  unfold initList machine initialCfg scanPeriodCfg labelCfg cfg initialData
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List OutputToken) :
    haltList machine output = haltCfg (finalData output) := by
  unfold haltList machine haltCfg finalData
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- A valid canonical normalized request executes to its exact semantic
complement-record block and leaves only the designated output tape nonempty. -/
def canonical_evalsInTime (request : Request)
    (valid : request.metadata.CursorValid) :
    EvalsToInTime (TM2.step program)
      (initialCfg
        (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request))
      (some (haltCfg (finalData (complementRecordBlock request))))
      (canonicalTotalTime request) := by
  have routed := canonicalRoute_evalsInTime request valid
  have finished := canonicalFinish_evalsInTime request
  have whole := EvalsToInTime.trans (TM2.step program)
    (canonicalRouteTime request) (canonicalFinishTime request)
    (initialCfg
      (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
        request))
    (cfg .reverseOutput (inputState .routeEnd)
      (canonicalAfterRouteData request))
    (some (haltCfg (finalData (complementRecordBlock request))))
    routed finished
  simpa [canonicalTotalTime, Nat.add_comm] using whole

/-- The finite machine realizes the semantic complement-record block on
every valid canonical normalized request. -/
def canonical_outputsInTime (request : Request)
    (valid : request.metadata.CursorValid) :
    TM2OutputsInTime machine
      (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock request)
      (some (complementRecordBlock request))
      (canonicalTotalTime request) := by
  have run := canonical_evalsInTime request valid
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind (TM2.step program))^[run.steps]
      (some (initList machine
        (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request))) =
        some (haltList machine (complementRecordBlock request))
  rw [initList_eq_initialCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
