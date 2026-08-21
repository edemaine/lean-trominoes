/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsRejectedFinishExecution
import LeanTrominoes.LastRepresentativeEqualityRowsSelectedFinishExecution

/-! # Complete last-representative row finish dispatch -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def finishTime (selected : Bool) (tokens : List Token) : Nat :=
  if selected then 2 * tokens.length + 3 else tokens.length + 2

def finish_evalsInTime (selected : Bool) (tokens : List Token)
    (data : TapeData) (rowReverseEq : data.rowReverse = tokens)
    (rowForwardEq : data.rowForward = []) :
    EvalsToInTime (TM2.step program) (finishRowCfg selected data)
      (some (scanStartCfg
        { data with
          rowIndex := () :: data.rowIndex
          rowReverse := []
          rowForward := []
          outputReverse :=
            if selected then tokens ++ data.outputReverse
            else data.outputReverse }))
      (finishTime selected tokens) := by
  cases selected with
  | false =>
      simpa [finishTime, rowForwardEq] using
        rejectedFinish_evalsInTime tokens data rowReverseEq
  | true =>
      simpa [finishTime] using
        selectedFinish_evalsInTime tokens data rowReverseEq rowForwardEq

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
