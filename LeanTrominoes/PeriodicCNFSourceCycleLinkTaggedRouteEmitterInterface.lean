/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecution

/-! # Finite-machine interface for tagged cycle-link route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem initList_eq_scanHeaderCfg (input : List InputSymbol) :
    initList machine input =
      scanHeaderCfg initialTag
        ⟨input, [], [], [], [], [], [], [], [], [], []⟩ := by
  unfold initList machine scanHeaderCfg cursorCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List OutputToken) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg haltDataCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_outputsInTime
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    TM2OutputsInTime machine (SourceCycleLinkTaggedRouteEmitter.encode input)
      (some (SourceCycleLinkTaggedRouteEmitter.emit input))
      (totalTime input) := by
  have run := execution input
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind machine.step)^[run.steps]
      (some (initList machine
        (SourceCycleLinkTaggedRouteEmitter.encode input))) =
        some (haltList machine
          (SourceCycleLinkTaggedRouteEmitter.emit input))
  rw [initList_eq_scanHeaderCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes

end
