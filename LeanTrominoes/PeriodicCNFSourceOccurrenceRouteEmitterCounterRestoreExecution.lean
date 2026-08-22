/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterExecutionData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterRestoreNilStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterRestoreConsStep
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport

/-! # Counter-restoration execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def restoreCounter_evalsInTime (stage : CounterStage)
    (cursor : Cursor) (data : TapeData) (scratch : List Unit)
    (scratchEq : data.scratch = scratch) :
    EvalsToInTime machine.step
      (restoreCounterCfg stage cursor data)
      (some (afterCounterCfg stage cursor
        (afterRestoreData data stage scratch)))
      (scratch.length + 1) := by
  induction scratch generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreCounter_nil stage cursor data scratchEq)
      simpa using step
  | cons head remaining induction =>
      cases head
      let nextData : TapeData :=
        { data.setCounter stage (() :: data.counter stage) with
          scratch := remaining }
      have first := oneStep
        (step_restoreCounter_cons stage cursor data remaining scratchEq)
      have nextScratchEq : nextData.scratch = remaining := by
        rfl
      have rest := induction nextData nextScratchEq
      have composed := EvalsToInTime.trans machine.step
        1 (remaining.length + 1)
        (restoreCounterCfg stage cursor data)
        (restoreCounterCfg stage cursor nextData)
        (some (afterCounterCfg stage cursor
          (afterRestoreData nextData stage remaining)))
        first rest
      simpa only [nextData, afterRestoreData_cons, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
