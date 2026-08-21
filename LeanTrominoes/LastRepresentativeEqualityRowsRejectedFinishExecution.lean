/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsRejectedExecution
import LeanTrominoes.LastRepresentativeEqualityRowsSuffixSteps

/-! # Finishing a rejected last-representative row -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def rejectedFinish_evalsInTime (tokens : List Token) (data : TapeData)
    (rowReverseEq : data.rowReverse = tokens) :
    EvalsToInTime (TM2.step program) (finishRowCfg false data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := [] }))
      (tokens.length + 2) := by
  have first := oneStep (step_finishRow_false data)
  have rest := clearRejectedRow_evalsInTime false tokens data rowReverseEq
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (tokens.length + 1)
    (finishRowCfg false data) (clearRejectedRowCfg false data)
    (some (scanStartCfg
      { data with
        rowIndex := () :: data.rowIndex
        rowReverse := [] }))
    first rest
  simpa [Nat.add_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
