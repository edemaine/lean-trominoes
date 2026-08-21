/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityListExecution
import LeanTrominoes.DelimitedBinaryWordPairEqualityReverseExecution

/-! # Complete execution of delimited binary-word equality -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

def totalTime (input : Input) : Nat :=
  pairsTime input.pairs + reverseTime (equalities input).reverse

theorem initList_eq_scanCfg (tokens : List Token) :
    initList machine tokens = scanCfg ⟨tokens, [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List Bool) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The fixed finite machine emits one equality bit for every encoded pair. -/
def machine_outputsInTime (input : Input) :
    TM2OutputsInTime machine (encode input)
      (some (equalities input)) (totalTime input) := by
  rcases input with ⟨pairs⟩
  let results := pairResults pairs
  have scanned := pairs_evalsInTime pairs [] []
  have scanned' : EvalsToInTime (TM2.step program)
      (scanCfg ⟨pairs.flatMap pairTokens, [], [], [], []⟩)
      (some (reverseCfg ⟨[], [], [], results.reverse, []⟩))
      (pairsTime pairs) := by
    simpa [results, pairResults] using scanned
  have reversed := reverse_evalsInTime results.reverse []
  have reversed' : EvalsToInTime (TM2.step program)
      (reverseCfg ⟨[], [], [], results.reverse, []⟩)
      (some (haltCfg results))
      (reverseTime results.reverse) := by
    simpa using reversed
  have whole := EvalsToInTime.trans (TM2.step program)
    (pairsTime pairs) (reverseTime results.reverse)
    (scanCfg ⟨pairs.flatMap pairTokens, [], [], [], []⟩)
    (reverseCfg ⟨[], [], [], results.reverse, []⟩)
    (some (haltCfg results)) scanned' reversed'
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step program))^[whole.steps]
        (some (initList machine (encode ⟨pairs⟩))) =
          some (haltList machine (equalities ⟨pairs⟩))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    change (flip bind (TM2.step program))^[whole.steps]
        (some (scanCfg
          ⟨pairs.flatMap pairTokens, [], [], [], []⟩)) =
          some (haltCfg results)
    exact whole.evals_in_steps
  · apply whole.steps_le_m.trans
    simp [totalTime, equalities, results, pairResults, Nat.add_comm]

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes

end
