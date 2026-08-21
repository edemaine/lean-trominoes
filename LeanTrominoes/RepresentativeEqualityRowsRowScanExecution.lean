/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsBoundedRowScanExecution
import LeanTrominoes.RepresentativeEqualityRowsShortRowScanExecution

/-! # Complete representative-row scanning -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

def rowScanTime (rowIndex : Nat) (row : List Bool) : Nat :=
  if rowIndex ≤ row.length then row.length + 2 else rowIndex + 1

/-- Scan a complete row for every possible row-index/width relationship. -/
def rowScan_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (scanPrefixCfg true data)
      (some (finishRowCfg
        (RepresentativeEqualityRows.selected rowIndex row)
        { data with
          input := tail
          prefixCountdown := []
          rowReverse :=
            .wordEnd :: (row.map .bit).reverse ++ data.rowReverse }))
      (rowScanTime rowIndex row) := by
  by_cases indexLe : rowIndex ≤ row.length
  · simpa [rowScanTime, indexLe] using
      boundedRowScan_evalsInTime rowIndex row tail data indexLe
        inputEq countdownEq
  · have indexGt : row.length < rowIndex := by omega
    simpa [rowScanTime, indexLe] using
      shortRowScan_evalsInTime rowIndex row tail data indexGt
        inputEq countdownEq

end RepresentativeEqualityRowsMachine
end LeanTrominoes
