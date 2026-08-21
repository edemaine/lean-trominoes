/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsOutputTransferExecution

/-! # Complete selected last-representative row transfer -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def moveSelected_evalsInTime (tokens : List Token) (data : TapeData)
    (rowReverseEq : data.rowReverse = tokens)
    (rowForwardEq : data.rowForward = []) :
    EvalsToInTime (TM2.step program) (moveSelectedToForwardCfg data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := []
          rowForward := []
          outputReverse := tokens ++ data.outputReverse }))
      (2 * tokens.length + 2) := by
  let forwarded : TapeData :=
    { data with
      rowReverse := []
      rowForward := tokens.reverse }
  have first := moveSelectedToForward_evalsInTime tokens data rowReverseEq
  have first' :
      EvalsToInTime (TM2.step program) (moveSelectedToForwardCfg data)
        (some (moveSelectedToOutputCfg forwarded))
        (tokens.length + 1) := by
    simpa [forwarded, rowForwardEq] using first
  have second := moveSelectedToOutput_evalsInTime tokens.reverse
    forwarded rfl
  have second' :
      EvalsToInTime (TM2.step program) (moveSelectedToOutputCfg forwarded)
        (some (scanStartCfg
          { data with
            rowIndex := () :: data.rowIndex
            rowReverse := []
            rowForward := []
            outputReverse := tokens ++ data.outputReverse }))
        (tokens.length + 1) := by
    simpa [forwarded, rowForwardEq] using second
  have composed := EvalsToInTime.trans (TM2.step program)
    (tokens.length + 1) (tokens.length + 1)
    (moveSelectedToForwardCfg data) (moveSelectedToOutputCfg forwarded)
    (some (scanStartCfg
      { data with
        rowIndex := () :: data.rowIndex
        rowReverse := []
        rowForward := []
        outputReverse := tokens ++ data.outputReverse }))
    first' second'
  have timeEq :
      (tokens.length + 1) + (tokens.length + 1) =
        2 * tokens.length + 2 := by
    omega
  simpa [timeEq] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
