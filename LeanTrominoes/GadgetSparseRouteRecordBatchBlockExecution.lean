/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchData
import LeanTrominoes.TM2EndDelimitedBlockMapBlockExecution

/-! # One canonical route request inside the block-map wrapper -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine
open TM2EndDelimitedBlockMap

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

noncomputable abbrev innerCompiler :=
  validRequestComputableInPolyTime

noncomputable abbrev machine : FinTM2 :=
  TM2EndDelimitedBlockMap.machine innerCompiler isEnd

/-- Exact wrapper cost after collection has found one complete request. -/
def blockRunTime (request : ValidRequest) : Nat :=
  (Fintype.card innerCompiler.tm.K + 1) +
    ((2 * (validRequestOutput request).length + 1) +
      (innerCompiler.time.eval (validRequestInput request).length +
        (2 * (validRequestInput request).length + 1)))

/-- Transfer, run, drain, and clean one canonical request, returning to the
outer collection state with its output accumulated in reverse. -/
def completeRequestRun (request : ValidRequest)
    (remaining : List InputToken) (outputReverse : List OutputToken) :
    EvalsToInTime machine.step
      (prepareCfg innerCompiler.tm InputToken OutputToken remaining
        (validRequestInput request).reverse
        (emptyInnerStacks innerCompiler.tm) outputReverse)
      (some (collectCfg innerCompiler.tm InputToken OutputToken remaining []
        (emptyInnerStacks innerCompiler.tm)
        ((validRequestOutput request).reverse ++ outputReverse)))
      (blockRunTime request) := by
  let prepared := prepareBlockRun innerCompiler isEnd
    (validRequestInput request) remaining outputReverse
  let computed := liftInnerEvalsToInTime innerCompiler isEnd
    remaining outputReverse (innerCompiler.outputsFun request)
  let preparedAndComputed := EvalsToInTime.trans machine.step
    (2 * (validRequestInput request).length + 1)
    (innerCompiler.time.eval (validRequestInput request).length)
    _ _ _ prepared computed
  let drained := drainEncodedHaltRun innerCompiler isEnd
    (validRequestOutput request) remaining outputReverse
  let throughDrain := EvalsToInTime.trans machine.step
    (innerCompiler.time.eval (validRequestInput request).length +
      (2 * (validRequestInput request).length + 1))
    (2 * (validRequestOutput request).length + 1)
    _ _ _ preparedAndComputed drained
  let cleaned := cleanupRun innerCompiler isEnd ⟨0, by omega⟩ remaining
    (emptyInnerStacks innerCompiler.tm)
    ((validRequestOutput request).reverse ++ outputReverse)
    (clearedBefore_zero innerCompiler.tm
      (emptyInnerStacks innerCompiler.tm))
  let whole := EvalsToInTime.trans machine.step
    ((2 * (validRequestOutput request).length + 1) +
      (innerCompiler.time.eval (validRequestInput request).length +
        (2 * (validRequestInput request).length + 1)))
    (cleanupMeasure innerCompiler.tm ⟨0, by omega⟩
      (emptyInnerStacks innerCompiler.tm) + 1)
    _ _ _ throughDrain cleaned
  simpa [blockRunTime, cleanupMeasure, innerPopulation,
    emptyInnerStacks] using whole

end GadgetSparseRouteRecordBatch
end
end LeanTrominoes
