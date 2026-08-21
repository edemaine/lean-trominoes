/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsOutputSteps

/-! # Row-counter restoration loop -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

/-- Restore every consumed row-counter marker and open the next output row. -/
def restoreRowCount_evalsInTime (tokens : List Unit) (data : TapeData)
    (restoreEq : data.rowRestore = tokens) :
    EvalsToInTime (TM2.step program) (restoreRowCountCfg data)
      (some (emitBitCfg
        { data with
          rowCountdown := tokens.reverse ++ data.rowCountdown
          rowRestore := []
          outputReverse := .wordStart :: data.outputReverse }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_restoreRowCount_nil data restoreEq)
      simpa using step
  | cons marker tokens induction =>
      rcases marker with ⟨⟩
      let nextData : TapeData :=
        { data with
          rowCountdown := () :: data.rowCountdown
          rowRestore := tokens }
      have first := oneStep
        (step_restoreRowCount_cons data tokens restoreEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (restoreRowCountCfg data) (restoreRowCountCfg nextData)
        (some (emitBitCfg
          { nextData with
            rowCountdown := tokens.reverse ++ nextData.rowCountdown
            rowRestore := []
            outputReverse := .wordStart :: nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end BoolSquareRowsMachine
end LeanTrominoes
