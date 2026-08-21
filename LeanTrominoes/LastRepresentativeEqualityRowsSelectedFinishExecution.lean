/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsSelectedExecution

/-! # Finishing a selected last-representative row -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def selectedFinish_evalsInTime (tokens : List Token) (data : TapeData)
    (rowReverseEq : data.rowReverse = tokens)
    (rowForwardEq : data.rowForward = []) :
    EvalsToInTime (TM2.step program) (finishRowCfg true data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := []
          rowForward := []
          outputReverse := tokens ++ data.outputReverse }))
      (2 * tokens.length + 3) := by
  have first := oneStep (step_finishRow_true data)
  have rest := moveSelected_evalsInTime tokens data
    rowReverseEq rowForwardEq
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (2 * tokens.length + 2)
    (finishRowCfg true data) (moveSelectedToForwardCfg data)
    (some (scanStartCfg
      { data with
        rowIndex := () :: data.rowIndex
        rowReverse := []
        rowForward := []
        outputReverse := tokens ++ data.outputReverse }))
    first rest
  simpa [Nat.add_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
