/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterData

/-! # Empty counter-copy step for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_copyCounter_nil (stage : CounterStage) (tag : Tag)
    (data : TapeData) (counterEq : data.counter stage = []) :
    machine.step (copyCounterCfg stage tag data) =
      some (restoreCounterCfg stage tag
        (data.setCounter stage [])) := by
  simp only [FinTM2.step, TM2.step, machine, copyCounterCfg,
    restoreCounterCfg, cursorCfg, cfg, program, TM2.stepAux]
  rw [tapes_counter, counterEq]
  simp only [CounterStage.units_nil, List.head?_nil, List.tail_nil,
    Option.map_none, unitIsNone, cursorTag, clear, cond_true]
  have updateEq := update_tapes_counter data stage []
  simp only [CounterStage.units_nil] at updateEq
  rw [updateEq]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
