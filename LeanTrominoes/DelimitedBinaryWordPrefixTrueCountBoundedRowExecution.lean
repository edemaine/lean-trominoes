/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountPrefixExecution
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountSuffixExecution

/-! # Counting a row prefix whose index lies within its width -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def boundedRow_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexLe : rowIndex ≤ row.length)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg data)
      (some (finishRowCfg
        { data with
          input := tail
          prefixCountdown := []
          outputReverse :=
            List.replicate
              (DelimitedBinaryWordPrefixTrueCounts.count rowIndex row)
              .unit ++ data.outputReverse }))
      (row.length + 2) := by
  let rowPrefix := row.take rowIndex
  let rowSuffix := row.drop rowIndex
  have prefixLength : rowPrefix.length = rowIndex := by
    simp [rowPrefix, List.length_take, indexLe]
  have rowSplit : rowPrefix ++ rowSuffix = row := by
    exact List.take_append_drop rowIndex row
  have mappedSplit :
      rowPrefix.map DelimitedBinaryWords.Token.bit ++
          rowSuffix.map DelimitedBinaryWords.Token.bit =
        row.map DelimitedBinaryWords.Token.bit := by
    rw [← List.map_append, rowSplit]
  have lengthSplit :
      rowPrefix.length + rowSuffix.length = row.length := by
    simpa using congrArg List.length rowSplit
  have inputSplit :
      data.input = rowPrefix.map .bit ++
        (rowSuffix.map .bit ++ .wordEnd :: tail) := by
    calc
      data.input = row.map .bit ++ .wordEnd :: tail := inputEq
      _ = (rowPrefix.map .bit ++ rowSuffix.map .bit) ++
          .wordEnd :: tail := by rw [← mappedSplit]
      _ = rowPrefix.map .bit ++
          (rowSuffix.map .bit ++ .wordEnd :: tail) := by
        rw [List.append_assoc]
  let afterPrefix : TapeData :=
    { data with
      input := rowSuffix.map .bit ++ .wordEnd :: tail
      prefixCountdown := []
      outputReverse :=
        List.replicate (rowPrefix.count true) .unit ++
          data.outputReverse }
  have first := scanPrefixBits_evalsInTime rowPrefix
    (rowSuffix.map .bit ++ .wordEnd :: tail) data inputSplit
    (by simpa [prefixLength] using countdownEq)
  have first' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg data)
        (some (scanSuffixCfg afterPrefix)) (rowPrefix.length + 1) := by
    simpa [afterPrefix] using first
  have second := scanSuffixBits_evalsInTime rowSuffix tail afterPrefix rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowPrefix.length + 1) (rowSuffix.length + 1)
    (scanPrefixCfg data) (scanSuffixCfg afterPrefix)
    (some (finishRowCfg { afterPrefix with input := tail }))
    first' second
  convert composed using 1
  · simp [afterPrefix, DelimitedBinaryWordPrefixTrueCounts.count,
      rowPrefix]
  · omega

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
