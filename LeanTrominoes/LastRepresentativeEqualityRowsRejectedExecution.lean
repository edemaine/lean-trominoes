/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsRejectedSteps

/-! # Complete rejected last-representative row clearing -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def clearRejectedRow_evalsInTime (representative : Bool)
    (tokens : List Token) (data : TapeData)
    (rowEq : data.rowReverse = tokens) :
    EvalsToInTime (TM2.step program)
      (clearRejectedRowCfg representative data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := [] }))
      (tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := oneStep
        (step_clearRejectedRow_nil representative data rowEq)
      simpa using step
  | cons token tokens induction =>
      let nextData : TapeData :=
        { data with rowReverse := tokens }
      have first := oneStep
        (step_clearRejectedRow_cons representative data token tokens rowEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (clearRejectedRowCfg representative data)
        (clearRejectedRowCfg representative nextData)
        (some (scanStartCfg
          { nextData with
            rowIndex := () :: nextData.rowIndex
            rowReverse := [] }))
        first rest
      simpa [nextData] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
