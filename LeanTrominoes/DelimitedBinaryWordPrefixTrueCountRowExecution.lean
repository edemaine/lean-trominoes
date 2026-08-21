/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountBoundedRowExecution
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountShortRowExecution

/-! # Unified row-prefix true-count execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def rowScanTime (rowIndex : Nat) (row : List Bool) : Nat :=
  if rowIndex ≤ row.length then row.length + 2 else rowIndex + 1

def row_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
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
      (rowScanTime rowIndex row) := by
  by_cases indexLe : rowIndex ≤ row.length
  · simpa [rowScanTime, indexLe] using
      boundedRow_evalsInTime rowIndex row tail data indexLe
        inputEq countdownEq
  · have indexGt : row.length < rowIndex := by omega
    simpa [rowScanTime, indexLe] using
      shortRow_evalsInTime rowIndex row tail data indexGt
        inputEq countdownEq

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
