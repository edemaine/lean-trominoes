/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountIndexSetupExecution

/-! # Opening a row for prefix counting -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def startRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq :
      data.input = DelimitedBinaryWords.wordTokens row ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (scanPrefixCfg
        { data with
          input := row.map .bit ++ .wordEnd :: tail
          rowIndex := List.replicate rowIndex ()
          indexRestore := []
          prefixCountdown := List.replicate rowIndex () }))
      (2 * rowIndex + 3) := by
  let opened : TapeData :=
    { data with input := row.map .bit ++ .wordEnd :: tail }
  have first := FiniteBlockTransducer.oneStep
    (step_scanStart_cons data .wordStart
      (row.map .bit ++ .wordEnd :: tail) (by
        simpa [DelimitedBinaryWords.wordTokens] using inputEq))
  have first' :
      EvalsToInTime (TM2.step program) (scanStartCfg data)
        (some (copyIndexCfg opened)) 1 := by
    simpa [opened] using first
  have rest := indexSetup_evalsInTime rowIndex opened
    (by simpa [opened] using indexEq)
    (by simpa [opened] using restoreEq)
    (by simpa [opened] using countdownEq)
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (2 * rowIndex + 2)
    (scanStartCfg data) (copyIndexCfg opened)
    (some (scanPrefixCfg
      { opened with
        rowIndex := List.replicate rowIndex ()
        indexRestore := []
        prefixCountdown := List.replicate rowIndex () }))
    first' rest
  simpa [opened, Nat.add_assoc] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
