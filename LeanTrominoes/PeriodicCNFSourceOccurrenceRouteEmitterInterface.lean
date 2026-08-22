/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecution

/-! # Finite-machine interface for source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem initList_eq_scanLeftCfg (input : List InputSymbol) :
    initList machine input =
      scanLeftCfg initialCursor
        ⟨input, [], [], [], [], [], [], [], [], [], [], []⟩ := by
  unfold initList machine scanLeftCfg cursorCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List OutputToken) :
    haltList machine output = haltCfg initialCursor output := by
  unfold haltList machine haltCfg haltDataCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_outputsInTime (input : SourceOccurrenceRouteEmitter.Input) :
    TM2OutputsInTime machine (SourceOccurrenceRouteEmitter.encode input)
      (some (SourceOccurrenceRouteEmitter.emit input)) (totalTime input) := by
  have run := execution input
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind machine.step)^[run.steps]
      (some (initList machine (SourceOccurrenceRouteEmitter.encode input))) =
        some (haltList machine (SourceOccurrenceRouteEmitter.emit input))
  rw [initList_eq_scanLeftCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
