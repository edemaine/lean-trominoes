/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsOutputSteps

/-! # Final output reversal -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

/-- Move every reversed output token onto the designated output stack. -/
def reverseOutput_evalsInTime (tokens output : List OutputToken) :
    EvalsToInTime (TM2.step program)
      (reverseOutputCfg
        ⟨[], [], [], [], [], [], [], [], [], tokens, output⟩)
      (some (haltCfg (tokens.reverse ++ output)))
      (tokens.length + 1) := by
  induction tokens generalizing output with
  | nil =>
      have step := oneStep (step_reverseOutput_nil output)
      simpa using step
  | cons token tokens induction =>
      have first := oneStep
        (step_reverseOutput_cons token tokens output)
      have rest := induction (token :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], [], [], token :: tokens, output⟩)
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], [], [], tokens, token :: output⟩)
        (some (haltCfg (tokens.reverse ++ token :: output)))
        first rest
      convert composed using 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp

end BoolSquareRowsMachine
end LeanTrominoes
