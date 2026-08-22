/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterCopyConsStep
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterCopyNilStep
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterExecutionData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecutionSupport

/-! # Counter-copy execution for tagged source cycle-link route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def copyCounter_evalsInTime (stage : CounterStage)
    (tag : Tag) (data : TapeData) (counter : List Unit)
    (counterEq : data.counter stage = counter) :
    EvalsToInTime machine.step
      (copyCounterCfg stage tag data)
      (some (restoreCounterCfg stage tag
        (afterCopyData data stage counter)))
      (counter.length + 1) := by
  induction counter generalizing data with
  | nil =>
      have step := oneStep
        (step_copyCounter_nil stage tag data counterEq)
      simpa using step
  | cons head remaining induction =>
      cases head
      let nextData : TapeData :=
        { data.setCounter stage remaining with
          scratch := () :: data.scratch
          outputReverse := .atomUnit :: data.outputReverse }
      have first := oneStep
        (step_copyCounter_cons stage tag data remaining counterEq)
      have nextCounterEq : nextData.counter stage = remaining := by
        simp only [nextData, TapeData.counter_setScratchOutputReverse,
          TapeData.counter_setCounter]
      have rest := induction nextData nextCounterEq
      have composed := EvalsToInTime.trans machine.step
        1 (remaining.length + 1)
        (copyCounterCfg stage tag data)
        (copyCounterCfg stage tag nextData)
        (some (restoreCounterCfg stage tag
          (afterCopyData nextData stage remaining)))
        first rest
      simpa only [nextData, afterCopyData_cons, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
