/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixSteps

/-! # Clearing an unused representative-row prefix countdown -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Clear every unary marker left after reaching a row delimiter early. -/
def clearPrefix_evalsInTime (representative : Bool) (tokens : List Unit)
    (data : TapeData) (countdownEq : data.prefixCountdown = tokens) :
    EvalsToInTime (TM2.step program) (clearPrefixCfg representative data)
      (some (finishRowCfg representative
        { data with prefixCountdown := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep
        (step_clearPrefix_nil representative data countdownEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with prefixCountdown := tokens }
      have first := oneStep
        (step_clearPrefix_cons representative data tokens countdownEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearPrefixCfg representative data)
        (clearPrefixCfg representative nextData)
        (some (finishRowCfg representative
          { nextData with prefixCountdown := [] }))
        first rest
      simpa [nextData] using composed

end RepresentativeEqualityRowsMachine
end LeanTrominoes
