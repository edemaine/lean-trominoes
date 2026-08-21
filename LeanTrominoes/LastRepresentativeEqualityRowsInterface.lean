/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsExecution

/-! # Finite-machine interface for last-representative rows -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

theorem initList_eq_scanStartCfg (input : List Token) :
    initList machine input =
      scanStartCfg ⟨input, [], [], [], [], [], [], []⟩ := by
  unfold initList machine scanStartCfg idleCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List Token) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_outputsInTime (input : DelimitedBinaryWords.Input) :
    TM2OutputsInTime machine (DelimitedBinaryWords.encode input)
      (some (DelimitedBinaryWords.encode
        (LastRepresentativeEqualityRows.rows input)))
      (totalTime input.words) := by
  have run := execution_evalsInTime input.words
  have semanticRun :
      EvalsToInTime (TM2.step program)
        (scanStartCfg
          ⟨DelimitedBinaryWords.encode input, [], [], [], [], [], [], []⟩)
        (some (haltCfg (DelimitedBinaryWords.encode
          (LastRepresentativeEqualityRows.rows input))))
        (totalTime input.words) := by
    simpa [LastRepresentativeEqualityRowTokens.tokensAux,
      LastRepresentativeEqualityRows.rows] using run
  refine
    { steps := semanticRun.steps
      evals_in_steps := ?_
      steps_le_m := semanticRun.steps_le_m }
  change (flip bind (TM2.step program))^[semanticRun.steps]
      (some (initList machine (DelimitedBinaryWords.encode input))) =
        some (haltList machine (DelimitedBinaryWords.encode
          (LastRepresentativeEqualityRows.rows input)))
  rw [initList_eq_scanStartCfg, haltList_eq_haltCfg]
  exact semanticRun.evals_in_steps

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes

end
