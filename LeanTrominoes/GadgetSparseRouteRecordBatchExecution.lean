/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchRequestExecution
import LeanTrominoes.TM2EndDelimitedBlockMapFinalizationExecution

/-! # Exact execution of a canonical route-request batch -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine
open TM2EndDelimitedBlockMap

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Exact recursive allowance from a canonical request suffix. -/
def runTime : List ValidRequest → List OutputToken → Nat
  | [], outputReverse => (2 * outputReverse.length + 1) + 1 + 1
  | request :: requests, outputReverse =>
      runTime requests
          ((validRequestOutput request).reverse ++ outputReverse) +
        requestRunTime request

/-- Process every canonical request and reverse the accumulated output. -/
def run (requests : List ValidRequest)
    (outputReverse : List OutputToken) :
    EvalsToInTime machine.step
      (collectCfg innerCompiler.tm InputToken OutputToken
        (input requests) [] (emptyInnerStacks innerCompiler.tm)
        outputReverse)
      (some (haltList machine
        (outputReverse.reverse ++ output requests)))
      (runTime requests outputReverse) := by
  induction requests generalizing outputReverse with
  | nil =>
      have collected := collectPartialRun innerCompiler isEnd [] []
        outputReverse (by simp)
      have finalized := finalizeRun innerCompiler isEnd [] outputReverse
      have whole := EvalsToInTime.trans machine.step
        1 ((2 * outputReverse.length + 1) + 1)
        _ _ _ collected finalized
      simpa [runTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using whole
  | cons request requests induction =>
      have first := requestRun request requests outputReverse
      have rest := induction
        ((validRequestOutput request).reverse ++ outputReverse)
      have whole := EvalsToInTime.trans machine.step
        (requestRunTime request)
        (runTime requests
          ((validRequestOutput request).reverse ++ outputReverse))
        _ _ _ first rest
      simpa [runTime, List.reverse_append, List.append_assoc,
        Nat.add_comm] using whole

theorem collectCfg_eq_initList (symbols : List InputToken) :
    collectCfg innerCompiler.tm InputToken OutputToken symbols []
        (emptyInnerStacks innerCompiler.tm) [] =
      initList machine symbols := by
  unfold collectCfg machine TM2EndDelimitedBlockMap.machine initList
  congr 1
  funext stack
  cases stack <;>
    simp [stackContents, emptyInnerStacks]

/-- Canonical batches reach the exact concatenated route-record output. -/
def machineRun (requests : List ValidRequest) :
    EvalsToInTime machine.step
      (initList machine (input requests))
      (some (haltList machine (output requests)))
      (runTime requests []) := by
  have execution := run requests []
  rw [collectCfg_eq_initList] at execution
  simpa using execution

end GadgetSparseRouteRecordBatch
end
end LeanTrominoes
