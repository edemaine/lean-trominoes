/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsForwardExecution

/-! # Second selected last-representative row transfer loop -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def moveSelectedToOutput_evalsInTime (tokens : List Token)
    (data : TapeData) (rowEq : data.rowForward = tokens) :
    EvalsToInTime (TM2.step program) (moveSelectedToOutputCfg data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowForward := []
          outputReverse := tokens.reverse ++ data.outputReverse }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_moveSelectedToOutput_nil data rowEq)
      simpa using step
  | cons token tokens induction =>
      let nextData : TapeData :=
        { data with
          rowForward := tokens
          outputReverse := token :: data.outputReverse }
      have first := oneStep
        (step_moveSelectedToOutput_cons data token tokens rowEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (moveSelectedToOutputCfg data)
        (moveSelectedToOutputCfg nextData)
        (some (scanStartCfg
          { nextData with
            rowIndex := () :: nextData.rowIndex
            rowForward := []
            outputReverse := tokens.reverse ++ nextData.outputReverse }))
        first rest
      simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
