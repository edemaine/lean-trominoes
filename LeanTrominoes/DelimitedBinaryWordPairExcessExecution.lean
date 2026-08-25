/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessListExecution
import LeanTrominoes.DelimitedBinaryWordPairExcessReverseExecution

/-! # Complete execution of unary word-pair excesses -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

def totalTime (keepFirst : Bool) (input : Input) : Nat :=
  pairsTime input.pairs +
    reverseTime
      (UnaryFieldEncoderMachine.unaryFields
        (excesses keepFirst input)).reverse

theorem initList_eq_scanCfg (keepFirst : Bool) (tokens : List Token) :
    initList (machine keepFirst) tokens =
      scanCfg ⟨tokens, [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (keepFirst : Bool)
    (output : List UnaryFieldEncoderMachine.Symbol) :
    haltList (machine keepFirst) output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The finite machine emits the selected canonical unary excess of every
encoded word pair. -/
def machine_outputsInTime (keepFirst : Bool) (input : Input) :
    TM2OutputsInTime (machine keepFirst) (encode input)
      (some (UnaryFieldEncoderMachine.unaryFields
        (excesses keepFirst input)))
      (totalTime keepFirst input) := by
  rcases input with ⟨pairs⟩
  let symbols := UnaryFieldEncoderMachine.unaryFields
    (pairExcesses keepFirst pairs)
  have scanned := pairs_evalsInTime keepFirst pairs [] []
  have scanned' : EvalsToInTime (TM2.step (program keepFirst))
      (scanCfg ⟨pairs.flatMap pairTokens, [], [], [], []⟩)
      (some (reverseOutputCfg ⟨[], [], [], symbols.reverse, []⟩))
      (pairsTime pairs) := by
    simpa [symbols, excesses, pairExcesses] using scanned
  have reversed := reverse_evalsInTime keepFirst symbols.reverse []
  have reversed' : EvalsToInTime (TM2.step (program keepFirst))
      (reverseOutputCfg ⟨[], [], [], symbols.reverse, []⟩)
      (some (haltCfg symbols))
      (reverseTime symbols.reverse) := by
    simpa using reversed
  have whole := EvalsToInTime.trans (TM2.step (program keepFirst))
    (pairsTime pairs) (reverseTime symbols.reverse)
    (scanCfg ⟨pairs.flatMap pairTokens, [], [], [], []⟩)
    (reverseOutputCfg ⟨[], [], [], symbols.reverse, []⟩)
    (some (haltCfg symbols)) scanned' reversed'
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program keepFirst)))^[whole.steps]
        (some (initList (machine keepFirst) (encode ⟨pairs⟩))) =
          some (haltList (machine keepFirst)
            (UnaryFieldEncoderMachine.unaryFields
              (excesses keepFirst ⟨pairs⟩)))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    change (flip bind (TM2.step (program keepFirst)))^[whole.steps]
        (some (scanCfg
          ⟨pairs.flatMap pairTokens, [], [], [], []⟩)) =
          some (haltCfg symbols)
    exact whole.evals_in_steps
  · apply whole.steps_le_m.trans
    simp [totalTime, symbols, excesses, pairExcesses, Nat.add_comm]

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes

end
