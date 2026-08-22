/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterData

/-! # Nonempty counter-copy step for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_copyCounter_cons (stage : CounterStage) (tag : Tag)
    (data : TapeData) (remaining : List Unit)
    (counterEq : data.counter stage = () :: remaining) :
    machine.step (copyCounterCfg stage tag data) =
      some (copyCounterCfg stage tag
        { data.setCounter stage remaining with
          scratch := () :: data.scratch
          outputReverse := .atomUnit :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, copyCounterCfg,
    cursorCfg, cfg, program, TM2.stepAux]
  rw [tapes_counter, counterEq]
  simp only [CounterStage.units_cons, List.head?_cons, List.tail_cons,
    Option.map_some, unitIsNone, cursorTag, clear, cond_false]
  have counterUpdateEq := update_tapes_counter data stage remaining
  rw [counterUpdateEq]
  simp only [tapes, TapeData.scratch_setCounter,
    TapeData.outputReverse_setCounter, update_tapes_scratch,
    update_tapes_outputReverse]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
