/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountRowExecution
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountStartExecution

/-! # Executing one complete row-prefix true count -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def oneRowTime (rowIndex : Nat) (row : List Bool) : Nat :=
  1 + (rowScanTime rowIndex row + (2 * rowIndex + 3))

def oneRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq :
      data.input = DelimitedBinaryWords.wordTokens row ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (scanStartCfg
        { data with
          input := tail
          rowIndex := List.replicate (rowIndex + 1) ()
          indexRestore := []
          prefixCountdown := []
          outputReverse :=
            .delimiter ::
              List.replicate
                (DelimitedBinaryWordPrefixTrueCounts.count rowIndex row)
                .unit ++ data.outputReverse }))
      (oneRowTime rowIndex row) := by
  let ready : TapeData :=
    { data with
      input := row.map .bit ++ .wordEnd :: tail
      rowIndex := List.replicate rowIndex ()
      indexRestore := []
      prefixCountdown := List.replicate rowIndex () }
  let scanned : TapeData :=
    { data with
      input := tail
      rowIndex := List.replicate rowIndex ()
      indexRestore := []
      prefixCountdown := []
      outputReverse :=
        List.replicate
          (DelimitedBinaryWordPrefixTrueCounts.count rowIndex row)
          .unit ++ data.outputReverse }
  have startRun := startRow_evalsInTime rowIndex row tail data
    inputEq indexEq restoreEq countdownEq
  have startRun' :
      EvalsToInTime (TM2.step program) (scanStartCfg data)
        (some (scanPrefixCfg ready)) (2 * rowIndex + 3) := by
    simpa [ready] using startRun
  have rowRun := row_evalsInTime rowIndex row tail ready rfl rfl
  have rowRun' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg ready)
        (some (finishRowCfg scanned)) (rowScanTime rowIndex row) := by
    simpa [ready, scanned] using rowRun
  have finishRun := FiniteBlockTransducer.oneStep (step_finishRow scanned)
  have throughRow := EvalsToInTime.trans (TM2.step program)
    (2 * rowIndex + 3) (rowScanTime rowIndex row)
    (scanStartCfg data) (scanPrefixCfg ready)
    (some (finishRowCfg scanned)) startRun' rowRun'
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowScanTime rowIndex row + (2 * rowIndex + 3)) 1
    (scanStartCfg data) (finishRowCfg scanned)
    (some (scanStartCfg
      { scanned with
        rowIndex := () :: scanned.rowIndex
        outputReverse := .delimiter :: scanned.outputReverse }))
    throughRow finishRun
  simpa [oneRowTime, scanned, List.replicate_succ] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
