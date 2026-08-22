/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterData

/-! # Empty counter-copy step for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_copyCounter_nil (stage : CounterStage) (cursor : Cursor)
    (data : TapeData) (counterEq : data.counter stage = []) :
    machine.step (copyCounterCfg stage cursor data) =
      some (restoreCounterCfg stage cursor
        (data.setCounter stage [])) := by
  simp only [FinTM2.step, TM2.step, machine, copyCounterCfg,
    restoreCounterCfg, cursorCfg, cfg, program, TM2.stepAux]
  rw [tapes_counter, counterEq]
  simp only [CounterStage.units_nil, List.head?_nil, List.tail_nil,
    Option.map_none, unitIsNone, cursorFromState, clear, cond_true]
  have updateEq := update_tapes_counter data stage []
  simp only [CounterStage.units_nil] at updateEq
  rw [updateEq]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
