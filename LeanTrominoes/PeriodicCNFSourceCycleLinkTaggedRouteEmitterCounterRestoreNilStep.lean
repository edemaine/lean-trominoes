/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterData

/-! # Empty counter-restoration step for tagged cycle-link emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_restoreCounter_nil (stage : CounterStage) (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    machine.step (restoreCounterCfg stage tag data) =
      some (afterCounterCfg stage tag { data with scratch := [] }) := by
  simp only [FinTM2.step, TM2.step, machine, restoreCounterCfg,
    cursorCfg, cfg, program, TM2.stepAux]
  have scratchTapeEq : tapes data .scratch = [] := by
    simpa only [tapes] using scratchEq
  rw [scratchTapeEq]
  simp only [List.head?_nil, List.tail_nil, unitIsNone, cond_true,
    cursorTag, clear]
  rw [update_tapes_scratch]
  cases stage <;>
    simp only [afterCounter, afterCounterCfg, copyCounterCfg,
      scanTargetCfg, finishTargetRecordCfg, cursorCfg, cfg, TM2.stepAux,
      update_tapes_outputReverse] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
