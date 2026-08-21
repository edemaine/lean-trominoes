/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsFinishExecution
import LeanTrominoes.LastRepresentativeEqualityRowsReadExecution

/-! # Execution of one complete last-representative row -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def oneRowTime (rowIndex : Nat) (row : List Bool) : Nat :=
  finishTime (LastRepresentativeEqualityRows.selected rowIndex row)
      (DelimitedBinaryWords.wordTokens row).reverse +
    rowReadTime rowIndex row

def oneRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq : data.input = DelimitedBinaryWords.wordTokens row ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = [])
    (rowReverseEq : data.rowReverse = [])
    (rowForwardEq : data.rowForward = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (scanStartCfg
        { data with
          input := tail
          rowIndex := List.replicate (rowIndex + 1) ()
          indexRestore := []
          prefixCountdown := []
          rowReverse := []
          rowForward := []
          outputReverse :=
            if LastRepresentativeEqualityRows.selected rowIndex row then
              (DelimitedBinaryWords.wordTokens row).reverse ++
                data.outputReverse
            else data.outputReverse }))
      (oneRowTime rowIndex row) := by
  let readData : TapeData :=
    { data with
      input := tail
      rowIndex := List.replicate rowIndex ()
      indexRestore := []
      prefixCountdown := []
      rowReverse := (DelimitedBinaryWords.wordTokens row).reverse }
  have first := readRow_evalsInTime rowIndex row tail data inputEq
    indexEq restoreEq countdownEq rowReverseEq
  have first' :
      EvalsToInTime (TM2.step program) (scanStartCfg data)
        (some (finishRowCfg
          (LastRepresentativeEqualityRows.selected rowIndex row) readData))
        (rowReadTime rowIndex row) := by
    simpa [readData] using first
  have second := finish_evalsInTime
    (LastRepresentativeEqualityRows.selected rowIndex row)
    (DelimitedBinaryWords.wordTokens row).reverse readData rfl
    (by simpa [readData] using rowForwardEq)
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowReadTime rowIndex row)
    (finishTime (LastRepresentativeEqualityRows.selected rowIndex row)
      (DelimitedBinaryWords.wordTokens row).reverse)
    (scanStartCfg data)
    (finishRowCfg
      (LastRepresentativeEqualityRows.selected rowIndex row) readData)
    (some (scanStartCfg
      { readData with
        rowIndex := () :: readData.rowIndex
        rowReverse := []
        rowForward := []
        outputReverse :=
          if LastRepresentativeEqualityRows.selected rowIndex row then
            (DelimitedBinaryWords.wordTokens row).reverse ++
              readData.outputReverse
          else readData.outputReverse }))
    first' second
  simpa [oneRowTime, readData, List.replicate_succ] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
