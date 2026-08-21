/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsDiagonalExecution
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixExecution
import Mathlib.Data.List.TakeDrop

/-! # Last-representative execution with an interior diagonal -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace LastRepresentativeEqualityRowsMachine

def interiorDiagonal_evalsInTime (rowIndex : Nat) (row : List Bool)
    (tail : List Token) (data : TapeData)
    (indexLt : rowIndex < row.length)
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
  let rowPrefix := row.take rowIndex
  let diagonal := row[rowIndex]
  let rowSuffix := row.drop (rowIndex + 1)
  have prefixLength : rowPrefix.length = rowIndex := by
    simp [rowPrefix, List.length_take, Nat.le_of_lt indexLt]
  have tailSplit : diagonal :: rowSuffix = row.drop rowIndex := by
    exact List.cons_getElem_drop_succ
  have rowSplit : rowPrefix ++ diagonal :: rowSuffix = row := by
    rw [tailSplit]
    exact List.take_append_drop rowIndex row
  have mappedSplit :
      rowPrefix.map DelimitedBinaryWords.Token.bit ++
          .bit diagonal ::
            rowSuffix.map DelimitedBinaryWords.Token.bit =
        row.map DelimitedBinaryWords.Token.bit := by
    rw [← List.map_cons, ← List.map_append, rowSplit]
  have reversedSplit :
      (row.map DelimitedBinaryWords.Token.bit).reverse =
        (rowSuffix.map DelimitedBinaryWords.Token.bit).reverse ++
          .bit diagonal ::
            (rowPrefix.map DelimitedBinaryWords.Token.bit).reverse := by
    rw [← mappedSplit, List.reverse_append, List.reverse_cons]
    simp [List.append_assoc]
  have lengthSplit :
      rowPrefix.length + 1 + rowSuffix.length = row.length := by
    have lengths := congrArg List.length rowSplit
    simp only [List.length_append, List.length_cons] at lengths
    omega
  have inputSplit :
      data.input =
        rowPrefix.map .bit ++
          (.bit diagonal ::
            rowSuffix.map .bit ++ .wordEnd :: tail) := by
    calc
      data.input = row.map .bit ++ .wordEnd :: tail := inputEq
      _ = (rowPrefix.map .bit ++
          .bit diagonal :: rowSuffix.map .bit) ++
            .wordEnd :: tail := by rw [← mappedSplit]
      _ = rowPrefix.map .bit ++
          (.bit diagonal ::
            rowSuffix.map .bit ++ .wordEnd :: tail) := by
        rw [List.append_assoc]
  let afterPrefix : TapeData :=
    { data with
      input := .bit diagonal ::
        rowSuffix.map .bit ++ .wordEnd :: tail
      prefixCountdown := []
      rowReverse :=
        (rowPrefix.map .bit).reverse ++ data.rowReverse }
  have first := skipPrefixBits_evalsInTime rowPrefix
    (.bit diagonal :: rowSuffix.map .bit ++ .wordEnd :: tail)
    data inputSplit (by simpa [prefixLength] using countdownEq)
  have first' :
      EvalsToInTime (TM2.step program) (skipPrefixCfg data)
        (some (skipDiagonalCfg afterPrefix)) (rowPrefix.length + 1) := by
    simpa [afterPrefix] using first
  have second := diagonalAndSuffix_evalsInTime diagonal rowSuffix tail
    afterPrefix rfl
  have selectedEq :
      LastRepresentativeEqualityRows.selected rowIndex row =
        !(rowSuffix.contains true) := by
    rfl
  have composed := EvalsToInTime.trans (TM2.step program)
    (rowPrefix.length + 1) (rowSuffix.length + 2)
    (skipPrefixCfg data) (skipDiagonalCfg afterPrefix)
    (some (finishRowCfg (!(rowSuffix.contains true))
      { afterPrefix with
        input := tail
        rowReverse :=
          .wordEnd :: (rowSuffix.map .bit).reverse ++
            .bit diagonal :: afterPrefix.rowReverse }))
    first' second
  convert composed using 1
  · simp only [afterPrefix]
    simp [selectedEq, reversedSplit, List.append_assoc]
  · omega

end LastRepresentativeEqualityRowsMachine
end LeanTrominoes
