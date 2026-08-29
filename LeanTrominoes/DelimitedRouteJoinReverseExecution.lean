/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinExecutionSupport
import LeanTrominoes.DelimitedRouteJoinOutputSteps

/-! # Output reversal for delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def reverseOutput_evalsInTime (tokens : List Token)
    (data : TapeData) (reverseEq : data.outputReverse = tokens) :
    EvalsToInTime machine.step (reverseOutputCfg data)
      (some ⟨none, .empty,
        tapes { data with
          outputReverse := []
          output := tokens.reverse ++ data.output }⟩)
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_reverseOutput_nil data reverseEq
      simpa using oneStep step
  | cons token tokens induction =>
      let popped := oneStep
        (step_reverseOutput_cons data token tokens reverseEq)
      let pushed := oneStep
        (step_pushOutput
          { data with outputReverse := tokens } token)
      let nextData : TapeData :=
        { data with
          outputReverse := tokens
          output := token :: data.output }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end LeanTrominoes.DelimitedRouteJoin

end
