/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterCopyExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterRestoreExecution

/-! # Counter round-trip execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def counterTime (counter : List Unit) : Nat :=
  counter.length + 1 + (counter.length + 1)

noncomputable def counter_evalsInTime (stage : CounterStage)
    (cursor : Cursor) (data : TapeData) (counter : List Unit)
    (counterEq : data.counter stage = counter)
    (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg stage cursor data)
      (some (afterCounterCfg stage cursor
        (afterCounterData data counter)))
      (counterTime counter) := by
  have throughCopy :=
    copyCounter_evalsInTime stage cursor data counter counterEq
  have copiedScratchEq :
      (afterCopyData data stage counter).scratch = counter.reverse := by
    simp only [afterCopyData, scratchEq, List.append_nil]
  have throughRestore :=
    restoreCounter_evalsInTime stage cursor
      (afterCopyData data stage counter) counter.reverse copiedScratchEq
  have whole := EvalsToInTime.trans machine.step
    (counter.length + 1) (counter.reverse.length + 1)
    (copyCounterCfg stage cursor data)
    (restoreCounterCfg stage cursor
      (afterCopyData data stage counter))
    (some (afterCounterCfg stage cursor
      (afterRestoreData (afterCopyData data stage counter) stage
        counter.reverse)))
    throughCopy throughRestore
  simpa only [afterRestoreData_afterCopyData data stage counter
      counterEq scratchEq,
    counterTime, List.length_reverse] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
