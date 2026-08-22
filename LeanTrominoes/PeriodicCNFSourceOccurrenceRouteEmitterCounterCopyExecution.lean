/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterCopyNilStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterCopyConsStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport

/-! # Counter-copy execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def copyCounter_evalsInTime (stage : CounterStage)
    (cursor : Cursor)
    (data : TapeData) (counter : List Unit)
    (counterEq : data.counter stage = counter) :
    EvalsToInTime machine.step
      (copyCounterCfg stage cursor data)
      (some (restoreCounterCfg stage cursor
        (afterCopyData data stage counter)))
      (counter.length + 1) := by
  induction counter generalizing data with
  | nil =>
      have step := oneStep
        (step_copyCounter_nil stage cursor data counterEq)
      simpa using step
  | cons head remaining induction =>
      cases head
      let nextData : TapeData :=
        { data.setCounter stage remaining with
          scratch := () :: data.scratch
          outputReverse := .atomUnit :: data.outputReverse }
      have first := oneStep
        (step_copyCounter_cons stage cursor data remaining counterEq)
      have nextCounterEq : nextData.counter stage = remaining := by
        simp only [nextData, TapeData.counter_setScratchOutputReverse,
          TapeData.counter_setCounter]
      have rest := induction nextData nextCounterEq
      have composed := EvalsToInTime.trans machine.step
        1 (remaining.length + 1)
        (copyCounterCfg stage cursor data)
        (copyCounterCfg stage cursor nextData)
        (some (restoreCounterCfg stage cursor
          (afterCopyData nextData stage remaining)))
        first rest
      simpa only [nextData, afterCopyData_cons, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
