/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSelectedSteps

/-! # First selected last-representative row transfer loop -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def moveSelectedToForward_evalsInTime (tokens : List Token)
    (data : TapeData) (rowEq : data.rowReverse = tokens) :
    EvalsToInTime (TM2.step program) (moveSelectedToForwardCfg data)
      (some (moveSelectedToOutputCfg
        { data with
          rowReverse := []
          rowForward := tokens.reverse ++ data.rowForward }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep (step_moveSelectedToForward_nil data rowEq)
      simpa using step
  | cons token tokens induction =>
      let nextData : TapeData :=
        { data with
          rowReverse := tokens
          rowForward := token :: data.rowForward }
      have first := oneStep
        (step_moveSelectedToForward_cons data token tokens rowEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (moveSelectedToForwardCfg data)
        (moveSelectedToForwardCfg nextData)
        (some (moveSelectedToOutputCfg
          { nextData with
            rowReverse := []
            rowForward := tokens.reverse ++ nextData.rowForward }))
        first rest
      simpa [nextData, List.reverse_cons, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
