/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductSetupExecution
import LeanTrominoes.DelimitedBinaryWordPairProductRowsExecution
import LeanTrominoes.DelimitedBinaryWordPairProductFinishExecution

/-! # Complete execution of the binary-word ordered product -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def totalTime (input : DelimitedBinaryWords.Input) : Nat :=
  let tokens := DelimitedBinaryWords.encode input
  let output := productTokens input.words input.words
  finishTime tokens output.reverse +
    (outerRowsTime input.words input.words + setupTime tokens)

theorem productTokens_eq_encode_pairs
    (input : DelimitedBinaryWords.Input) :
    productTokens input.words input.words =
      DelimitedBinaryWordPairs.encode (pairs input) := by
  rcases input with ⟨words⟩
  simp [productTokens, rowTokens, pairs,
    DelimitedBinaryWordPairs.encode, List.flatMap_assoc,
    List.flatMap_map]

theorem initList_eq_copyInputCfg (tokens : List WordToken) :
    initList machine tokens =
      copyInputCfg ⟨tokens, [], [], [], [], [], [], [], []⟩ := by
  unfold initList machine copyInputCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List PairToken) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

/-- The fixed finite machine emits every ordered pair of encoded words in
row-major order. -/
def machine_outputsInTime (input : DelimitedBinaryWords.Input) :
    TM2OutputsInTime machine (DelimitedBinaryWords.encode input)
      (some (DelimitedBinaryWordPairs.encode (pairs input)))
      (totalTime input) := by
  rcases input with ⟨words⟩
  let tokens :=
    DelimitedBinaryWords.encode (DelimitedBinaryWords.Input.mk words)
  let output := productTokens words words
  have setupRun := setup_evalsInTime tokens
  have rowsRun := outerRows_evalsInTime words [] words
    ⟨[], [], tokens, tokens, [], [], [], [], []⟩
    (by simp [tokens, DelimitedBinaryWords.encode])
    (by simp [tokens, DelimitedBinaryWords.encode]) rfl rfl rfl
  have throughRows := EvalsToInTime.trans (TM2.step program)
    (setupTime tokens) (outerRowsTime words words)
    (copyInputCfg ⟨tokens, [], [], [], [], [], [], [], []⟩)
    (scanOuterCfg ⟨[], [], tokens, tokens, [], [], [], [], []⟩)
    (some (scanOuterCfg
      ⟨[], [], [], tokens, [], [], [], output.reverse, []⟩))
    setupRun (by simpa [tokens, output,
      DelimitedBinaryWords.encode] using rowsRun)
  have finishRun := finish_evalsInTime tokens output.reverse
  have whole := EvalsToInTime.trans (TM2.step program)
    (outerRowsTime words words + setupTime tokens)
    (finishTime tokens output.reverse)
    (copyInputCfg ⟨tokens, [], [], [], [], [], [], [], []⟩)
    (scanOuterCfg
      ⟨[], [], [], tokens, [], [], [], output.reverse, []⟩)
    (some (haltCfg output))
    throughRows (by simpa [output] using finishRun)
  have outputEq :
      DelimitedBinaryWordPairs.encode
          (pairs (DelimitedBinaryWords.Input.mk words)) = output := by
    symm
    simpa [output] using
      productTokens_eq_encode_pairs
        (DelimitedBinaryWords.Input.mk words)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step program))^[whole.steps]
        (some (initList machine
          (DelimitedBinaryWords.encode
            (DelimitedBinaryWords.Input.mk words)))) =
        some (haltList machine
          (DelimitedBinaryWordPairs.encode
            (pairs (DelimitedBinaryWords.Input.mk words))))
    rw [initList_eq_copyInputCfg, haltList_eq_haltCfg]
    rw [show DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words) = tokens by rfl,
      outputEq]
    exact whole.evals_in_steps
  · apply whole.steps_le_m.trans
    simp [totalTime, tokens, output]

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes

end
