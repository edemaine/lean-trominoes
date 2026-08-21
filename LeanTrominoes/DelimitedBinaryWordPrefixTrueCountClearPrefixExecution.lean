/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountPrefixSteps

/-! # Clearing an unused row-prefix countdown -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def clearPrefix_evalsInTime (tokens : List Unit) (data : TapeData)
    (countdownEq : data.prefixCountdown = tokens) :
    EvalsToInTime (TM2.step program) (clearPrefixCfg data)
      (some (finishRowCfg { data with prefixCountdown := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := FiniteBlockTransducer.oneStep
        (step_clearPrefix_nil data countdownEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with prefixCountdown := tokens }
      have first := FiniteBlockTransducer.oneStep
        (step_clearPrefix_cons data tokens countdownEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearPrefixCfg data) (clearPrefixCfg nextData)
        (some (finishRowCfg { nextData with prefixCountdown := [] }))
        first rest
      simpa [nextData] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
