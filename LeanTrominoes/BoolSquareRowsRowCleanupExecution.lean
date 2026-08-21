/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsOutputSteps

/-! # Row-counter cleanup loops -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def clearRowCountdown_evalsInTime (tokens : List Unit) (data : TapeData)
    (countdownEq : data.rowCountdown = tokens) :
    EvalsToInTime (TM2.step program) (clearRowCountdownCfg data)
      (some (clearRowRestoreCfg { data with rowCountdown := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearRowCountdown_nil data countdownEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData := { data with rowCountdown := tokens }
      have first := oneStep
        (step_clearRowCountdown_cons data tokens countdownEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearRowCountdownCfg data) (clearRowCountdownCfg nextData)
        (some (clearRowRestoreCfg { nextData with rowCountdown := [] }))
        first rest
      simpa [nextData] using composed

def clearRowRestore_evalsInTime (tokens : List Unit) (data : TapeData)
    (restoreEq : data.rowRestore = tokens) :
    EvalsToInTime (TM2.step program) (clearRowRestoreCfg data)
      (some (reverseOutputCfg { data with rowRestore := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_clearRowRestore_nil data restoreEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData := { data with rowRestore := tokens }
      have first := oneStep
        (step_clearRowRestore_cons data tokens restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearRowRestoreCfg data) (clearRowRestoreCfg nextData)
        (some (reverseOutputCfg { nextData with rowRestore := [] }))
        first rest
      simpa [nextData] using composed

end BoolSquareRowsMachine
end LeanTrominoes
