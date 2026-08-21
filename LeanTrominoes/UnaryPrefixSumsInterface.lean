/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsExecution

/-! # Finite-machine interface for unary prefix sums -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

theorem initList_eq_readFieldCfg (input : List Symbol) :
    initList machine input =
      readFieldCfg ⟨input, [], [], [], []⟩ := by
  unfold initList machine readFieldCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltDataCfg (output : List Symbol) :
    haltList machine output =
      haltDataCfg ⟨[], [], [], [], output⟩ := by
  unfold haltList machine haltDataCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The fixed finite machine emits the stable starting offset of every unary
input field. -/
def machine_outputsInTime (values : List Nat) :
    TM2OutputsInTime machine
      (UnaryFieldEncoderMachine.unaryFields values)
      (some (UnaryFieldEncoderMachine.unaryFields
        (PrefixSums.starts values)))
      (totalTime values) := by
  have run := execution values
  have semanticRun :
      EvalsToInTime (TM2.step program)
        (readFieldCfg
          ⟨UnaryFieldEncoderMachine.unaryFields values, [], [], [], []⟩)
        (some (haltDataCfg
          ⟨[], [], [], [],
            UnaryFieldEncoderMachine.unaryFields
              (PrefixSums.starts values)⟩))
        (totalTime values) := by
    simpa [outputWord] using run
  refine
    { steps := semanticRun.steps
      evals_in_steps := ?_
      steps_le_m := semanticRun.steps_le_m }
  change (flip bind (TM2.step program))^[semanticRun.steps]
      (some (initList machine
        (UnaryFieldEncoderMachine.unaryFields values))) =
        some (haltList machine
          (UnaryFieldEncoderMachine.unaryFields
            (PrefixSums.starts values)))
  rw [initList_eq_readFieldCfg, haltList_eq_haltDataCfg]
  exact semanticRun.evals_in_steps

end UnaryPrefixSumsMachine
end LeanTrominoes

end
