/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsIndexSetupExecution

/-! # Opening a row and preparing its last-representative index -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def startRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq : data.input = DelimitedBinaryWords.wordTokens row ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = [])
    (rowReverseEq : data.rowReverse = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (skipPrefixCfg
        { data with
          input := row.map .bit ++ .wordEnd :: tail
          rowIndex := List.replicate rowIndex ()
          indexRestore := []
          prefixCountdown := List.replicate rowIndex ()
          rowReverse := [.wordStart] }))
      (2 * rowIndex + 3) := by
  let opened : TapeData :=
    { data with
      input := row.map .bit ++ .wordEnd :: tail
      rowReverse := [.wordStart] }
  have first := oneStep
    (step_scanStart_cons data .wordStart
      (row.map .bit ++ .wordEnd :: tail) (by
        simpa [DelimitedBinaryWords.wordTokens] using inputEq))
  have first' :
      EvalsToInTime (TM2.step program) (scanStartCfg data)
        (some (copyIndexCfg opened)) 1 := by
    simpa [opened, rowReverseEq] using first
  have rest := indexSetup_evalsInTime rowIndex opened
    (by simpa [opened] using indexEq)
    (by simpa [opened] using restoreEq)
    (by simpa [opened] using countdownEq)
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (2 * rowIndex + 2)
    (scanStartCfg data) (copyIndexCfg opened)
    (some (skipPrefixCfg
      { opened with
        rowIndex := List.replicate rowIndex ()
        indexRestore := []
        prefixCountdown := List.replicate rowIndex () }))
    first' rest
  simpa [opened, Nat.add_assoc] using composed

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
