/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchBlockExecution
import LeanTrominoes.TM2EndDelimitedBlockMapCollectionExecution

/-! # Collection and execution of one canonical route request -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine
open TM2EndDelimitedBlockMap

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def requestRunTime (request : ValidRequest) : Nat :=
  blockRunTime request + 2 * (requestBody request).length + 2

/-- Collect and execute the first request of a canonical batch. -/
def requestRun (request : ValidRequest) (requests : List ValidRequest)
    (outputReverse : List OutputToken) :
    EvalsToInTime machine.step
      (collectCfg innerCompiler.tm InputToken OutputToken
        (input (request :: requests)) []
        (emptyInnerStacks innerCompiler.tm) outputReverse)
      (some (collectCfg innerCompiler.tm InputToken OutputToken
        (input requests) [] (emptyInnerStacks innerCompiler.tm)
        ((validRequestOutput request).reverse ++ outputReverse)))
      (requestRunTime request) := by
  have collected := collectCompleteRun innerCompiler isEnd
    (requestBody request) .routeEnd (input requests) [] outputReverse
    (requestBody_continues request) isEnd_routeEnd
  have collected' : EvalsToInTime machine.step
      (collectCfg innerCompiler.tm InputToken OutputToken
        (input (request :: requests)) []
        (emptyInnerStacks innerCompiler.tm) outputReverse)
      (some (prepareCfg innerCompiler.tm InputToken OutputToken
        (input requests) (validRequestInput request).reverse
        (emptyInnerStacks innerCompiler.tm) outputReverse))
      (2 * (requestBody request).length + 2) := by
    simpa [validRequestInput_eq_body, List.reverse_append] using collected
  have completed := completeRequestRun request (input requests) outputReverse
  have whole := EvalsToInTime.trans machine.step
    (2 * (requestBody request).length + 2)
    (blockRunTime request)
    _ _ _ collected' completed
  simpa [requestRunTime, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using whole

end GadgetSparseRouteRecordBatch
end
end LeanTrominoes
