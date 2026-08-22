/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterData

/-! # Nonempty counter-restoration step for tagged cycle-link emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_restoreCounter_cons (stage : CounterStage) (tag : Tag)
    (data : TapeData) (remaining : List Unit)
    (scratchEq : data.scratch = () :: remaining) :
    machine.step (restoreCounterCfg stage tag data) =
      some (restoreCounterCfg stage tag
        { data.setCounter stage (() :: data.counter stage) with
          scratch := remaining }) := by
  simp only [FinTM2.step, TM2.step, machine, restoreCounterCfg,
    cursorCfg, cfg, program, TM2.stepAux]
  have scratchTapeEq : tapes data .scratch = () :: remaining := by
    simpa only [tapes] using scratchEq
  rw [scratchTapeEq]
  simp only [List.head?_cons, List.tail_cons, unitIsNone, cond_false]
  rw [update_tapes_scratch]
  rw [tapes_counter]
  simp only [TapeData.counter_setScratch]
  rw [← CounterStage.units_cons]
  rw [update_tapes_counter]
  rw [TapeData.setCounter_setScratch]
  simp only [cursorTag, clear]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
