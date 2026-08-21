/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualitySteps

/-! # Output reversal for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

def reverseTime (word : List Bool) : Nat := word.length + 1

def reverse_evalsInTime (word output : List Bool) :
    EvalsToInTime (TM2.step program)
      (reverseCfg ⟨[], [], [], word, output⟩)
      (some (haltCfg (word.reverse ++ output)))
      (reverseTime word) := by
  induction word generalizing output with
  | nil =>
      have step := oneStep (step_reverse_nil output)
      convert step using 1 <;> simp [reverseTime]
  | cons bit word induction =>
      have first := oneStep (step_reverse_cons
        ⟨[], [], [], bit :: word, output⟩ bit word rfl)
      have rest := induction (bit :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (reverseTime word)
        (reverseCfg ⟨[], [], [], bit :: word, output⟩)
        (reverseCfg ⟨[], [], [], word, bit :: output⟩)
        (some (haltCfg (word.reverse ++ bit :: output)))
        first rest
      simpa only [reverseTime, List.length_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append, Nat.add_comm]
        using composed

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
