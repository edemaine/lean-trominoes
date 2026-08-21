/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterExecution

/-! # Finite-machine interface for unary successor-equality filtering -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

theorem initList_eq_scanLeftCfg (input : List InputSymbol) :
    initList machine input =
      scanLeftCfg ⟨input, [], [], [], [], [], [], []⟩ := by
  unfold initList machine scanLeftCfg emptyCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List UnarySymbol) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The fixed finite machine emits the size field exactly at positions where
`size = rank + 1`, and emits zero fields elsewhere. -/
def machine_outputsInTime (input : Input) :
    TM2OutputsInTime machine (encode input)
      (some (outputEncoding input)) (totalTime input) := by
  have run := execution input
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind machine.step)^[run.steps]
      (some (initList machine (encode input))) =
        some (haltList machine (outputEncoding input))
  rw [initList_eq_scanLeftCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
