/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsInteriorDiagonalExecution
import LeanTrominoes.LastRepresentativeEqualityRowsTerminalDiagonalExecution

/-! # Scanning a row whose diagonal index is within its width -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def boundedRowScan_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexLe : rowIndex ≤ row.length)
    (inputEq : data.input = row.map .bit ++ .wordEnd :: tail)
    (countdownEq :
      data.prefixCountdown = List.replicate rowIndex ()) :
    EvalsToInTime (TM2.step program) (skipPrefixCfg data)
      (some (finishRowCfg
        (LastRepresentativeEqualityRows.selected rowIndex row)
        { data with
          input := tail
          prefixCountdown := []
          rowReverse :=
            .wordEnd :: (row.map .bit).reverse ++ data.rowReverse }))
      (row.length + 2) := by
  by_cases atEnd : rowIndex = row.length
  · subst rowIndex
    have run := terminalDiagonal_evalsInTime row tail data
      inputEq countdownEq
    have selectedTrue :
        LastRepresentativeEqualityRows.selected row.length row = true := by
      simp [LastRepresentativeEqualityRows.selected,
        List.drop_eq_nil_of_le (by omega : row.length ≤ row.length + 1)]
    simpa [selectedTrue] using run
  · have indexLt : rowIndex < row.length := by
      omega
    exact interiorDiagonal_evalsInTime rowIndex row tail data
      indexLt inputEq countdownEq

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
