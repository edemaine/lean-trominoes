/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductCleanupSteps

/-! # Output reversal for the binary-word ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def reverseTime (word : List PairToken) : Nat := word.length + 1

def reverseOutput_evalsInTime (word output : List PairToken) :
    EvalsToInTime (TM2.step program)
      (reverseOutputCfg ⟨[], [], [], [], [], [], [], word, output⟩)
      (some (haltCfg (word.reverse ++ output)))
      (reverseTime word) := by
  induction word generalizing output with
  | nil =>
      have step := oneStep (step_reverseOutput_nil output)
      convert step using 1 <;> simp [reverseTime]
  | cons token word induction =>
      have first := oneStep (step_reverseOutput_cons
        ⟨[], [], [], [], [], [], [], token :: word, output⟩
        token word rfl)
      have rest := induction (token :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (reverseTime word)
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], token :: word, output⟩)
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], word, token :: output⟩)
        (some (haltCfg (word.reverse ++ token :: output)))
        first rest
      simpa only [reverseTime, List.length_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append, Nat.add_comm]
        using composed

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
