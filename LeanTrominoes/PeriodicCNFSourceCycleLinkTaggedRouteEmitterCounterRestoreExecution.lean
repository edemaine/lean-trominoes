/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterExecutionData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterRestoreConsStep
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterRestoreNilStep
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecutionSupport

/-! # Counter-restoration execution for tagged cycle-link route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def restoreCounter_evalsInTime (stage : CounterStage)
    (tag : Tag) (data : TapeData) (scratch : List Unit)
    (scratchEq : data.scratch = scratch) :
    EvalsToInTime machine.step
      (restoreCounterCfg stage tag data)
      (some (afterCounterCfg stage tag
        (afterRestoreData data stage scratch)))
      (scratch.length + 1) := by
  induction scratch generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreCounter_nil stage tag data scratchEq)
      simpa using step
  | cons head remaining induction =>
      cases head
      let nextData : TapeData :=
        { data.setCounter stage (() :: data.counter stage) with
          scratch := remaining }
      have first := oneStep
        (step_restoreCounter_cons stage tag data remaining scratchEq)
      have nextScratchEq : nextData.scratch = remaining := by
        rfl
      have rest := induction nextData nextScratchEq
      have composed := EvalsToInTime.trans machine.step
        1 (remaining.length + 1)
        (restoreCounterCfg stage tag data)
        (restoreCounterCfg stage tag nextData)
        (some (afterCounterCfg stage tag
          (afterRestoreData nextData stage remaining)))
        first rest
      simpa only [nextData, afterRestoreData_cons, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
