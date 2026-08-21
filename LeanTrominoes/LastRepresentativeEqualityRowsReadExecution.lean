/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsRowScanExecution
import LeanTrominoes.LastRepresentativeEqualityRowsStartExecution

/-! # Reading one complete last-representative row -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def rowReadTime (rowIndex : Nat) (row : List Bool) : Nat :=
  rowScanTime rowIndex row + (2 * rowIndex + 3)

def readRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq : data.input = DelimitedBinaryWords.wordTokens row ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = [])
    (rowReverseEq : data.rowReverse = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (finishRowCfg
        (LastRepresentativeEqualityRows.selected rowIndex row)
        { data with
          input := tail
          rowIndex := List.replicate rowIndex ()
          indexRestore := []
          prefixCountdown := []
          rowReverse := (DelimitedBinaryWords.wordTokens row).reverse }))
      (rowReadTime rowIndex row) := by
  let ready : TapeData :=
    { data with
      input := row.map .bit ++ .wordEnd :: tail
      rowIndex := List.replicate rowIndex ()
      indexRestore := []
      prefixCountdown := List.replicate rowIndex ()
      rowReverse := [.wordStart] }
  have first := startRow_evalsInTime rowIndex row tail data inputEq
    indexEq restoreEq countdownEq rowReverseEq
  have first' :
      EvalsToInTime (TM2.step program) (scanStartCfg data)
        (some (skipPrefixCfg ready)) (2 * rowIndex + 3) := by
    simpa [ready] using first
  have second := rowScan_evalsInTime rowIndex row tail ready rfl rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    (2 * rowIndex + 3) (rowScanTime rowIndex row)
    (scanStartCfg data) (skipPrefixCfg ready)
    (some (finishRowCfg
      (LastRepresentativeEqualityRows.selected rowIndex row)
      { ready with
        input := tail
        prefixCountdown := []
        rowReverse :=
          .wordEnd :: (row.map .bit).reverse ++ ready.rowReverse }))
    first' second
  simpa [rowReadTime, ready, DelimitedBinaryWords.wordTokens,
    List.reverse_append, List.append_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
