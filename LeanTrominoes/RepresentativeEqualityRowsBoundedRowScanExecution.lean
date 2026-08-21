/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsPrefixExecution
import LeanTrominoes.RepresentativeEqualityRowsSuffixExecution

/-! # Scanning a row whose diagonal index lies within its width -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

/-- Scan a complete row when its unary index does not exceed its width. -/
def boundedRowScan_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexLe : rowIndex ≤ row.length)
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
  have reversedSplit :
      (row.map DelimitedBinaryWords.Token.bit).reverse =
        (rowSuffix.map DelimitedBinaryWords.Token.bit).reverse ++
          (rowPrefix.map DelimitedBinaryWords.Token.bit).reverse := by
    rw [← mappedSplit, List.reverse_append]
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
      rowReverse := (rowPrefix.map .bit).reverse ++ data.rowReverse }
  have first := scanPrefixBits_evalsInTime true rowPrefix
    (rowSuffix.map .bit ++ .wordEnd :: tail) data inputSplit
    (by simpa [prefixLength] using countdownEq)
  have first' :
      EvalsToInTime (TM2.step program) (scanPrefixCfg true data)
        (some (scanSuffixCfg
          (RepresentativeEqualityRows.selected rowIndex row)
          afterPrefix))
        (rowPrefix.length + 1) := by
    simpa [afterPrefix, RepresentativeEqualityRows.selected, rowPrefix]
      using first
  have second := scanSuffixBits_evalsInTime
    (RepresentativeEqualityRows.selected rowIndex row) rowSuffix tail
    afterPrefix rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowPrefix.length + 1) (rowSuffix.length + 1)
    (scanPrefixCfg true data)
    (scanSuffixCfg (RepresentativeEqualityRows.selected rowIndex row)
      afterPrefix)
    (some (finishRowCfg
      (RepresentativeEqualityRows.selected rowIndex row)
      { afterPrefix with
        input := tail
        rowReverse :=
          .wordEnd :: (rowSuffix.map .bit).reverse ++
            afterPrefix.rowReverse }))
    first' second
  convert composed using 1
  · simp only [afterPrefix]
    simp [reversedSplit, List.append_assoc]
  · omega

end RepresentativeEqualityRowsMachine
end LeanTrominoes
