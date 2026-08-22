/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapPreparationExecution
import LeanTrominoes.TM2EndDelimitedBlockMapInnerExecution
import LeanTrominoes.TM2EndDelimitedBlockMapDrainExecution
import LeanTrominoes.TM2EndDelimitedBlockMapCleanupExecution

/-! # Complete-block executions of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open scoped BigOperators

open Computability StateTransition Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

section

variable {Source Target : Type}
variable [Fintype Source] [Fintype Target]
variable [Inhabited Source] [Inhabited Target]
variable {function : List Source → List Target}

def blockRunTime (inner : TM2ComputableInPolyTime id id function)
    (block : List Source) : Nat :=
  (Fintype.card inner.tm.K + 1) +
    ((2 * (function block).length + 1) +
      (inner.time.eval block.length + (2 * block.length + 1)))

/-- Run the inner compiler on one complete block and return to collection
with all inner stacks empty. -/
def completeBlockRun
    (inner : TM2ComputableInPolyTime id id function)
    (isEnd : Source → Bool)
    (block input : List Source) (outputReverse : List Target) :
    EvalsToInTime (machine inner isEnd).step
      (prepareCfg inner.tm Source Target input block.reverse
        (emptyInnerStacks inner.tm) outputReverse)
      (some (collectCfg inner.tm Source Target input []
        (emptyInnerStacks inner.tm)
        ((function block).reverse ++ outputReverse)))
      (blockRunTime inner block) := by
  let prepared := prepareBlockRun inner isEnd block input outputReverse
  let computed := liftInnerEvalsToInTime inner isEnd input outputReverse
    (inner.outputsFun block)
  let preparedAndComputed := EvalsToInTime.trans
    (machine inner isEnd).step
    (2 * block.length + 1) (inner.time.eval block.length)
    _ _ _ prepared computed
  let drained := drainEncodedHaltRun inner isEnd
    (function block) input outputReverse
  let throughDrain := EvalsToInTime.trans (machine inner isEnd).step
    (inner.time.eval block.length + (2 * block.length + 1))
    (2 * (function block).length + 1)
    _ _ _ preparedAndComputed drained
  let cleaned := cleanupRun inner isEnd ⟨0, by omega⟩ input
    (emptyInnerStacks inner.tm)
    ((function block).reverse ++ outputReverse)
    (clearedBefore_zero inner.tm (emptyInnerStacks inner.tm))
  let whole := EvalsToInTime.trans (machine inner isEnd).step
    ((2 * (function block).length + 1) +
      (inner.time.eval block.length + (2 * block.length + 1)))
    (cleanupMeasure inner.tm ⟨0, by omega⟩
      (emptyInnerStacks inner.tm) + 1)
    _ _ _ throughDrain cleaned
  simpa [blockRunTime, cleanupMeasure, innerPopulation,
    emptyInnerStacks] using whole

end

end TM2EndDelimitedBlockMap
end LeanTrominoes
