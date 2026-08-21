/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountOneRowExecution

/-! # Executing all row-prefix true counts -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def rowsTime : Nat → List (List Bool) → Nat
  | _, [] => 0
  | rowIndex, row :: rows =>
      rowsTime (rowIndex + 1) rows + oneRowTime rowIndex row

def rows_evalsInTime (rowIndex : Nat) (rows : List (List Bool))
    (tail : List Token) (data : TapeData)
    (inputEq :
      data.input = DelimitedBinaryWords.encode ⟨rows⟩ ++ tail)
    (indexEq : data.rowIndex = List.replicate rowIndex ())
    (restoreEq : data.indexRestore = [])
    (countdownEq : data.prefixCountdown = []) :
    EvalsToInTime (TM2.step program) (scanStartCfg data)
      (some (scanStartCfg
        { data with
          input := tail
          rowIndex := List.replicate (rowIndex + rows.length) ()
          indexRestore := []
          prefixCountdown := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (DelimitedBinaryWordPrefixTrueCounts.countsAux
                rowIndex rows)).reverse ++ data.outputReverse }))
      (rowsTime rowIndex rows) := by
  induction rows generalizing rowIndex data with
  | nil =>
      have run := EvalsToInTime.refl (TM2.step program)
        (scanStartCfg data)
      have dataEq :
          { data with
            input := tail
            rowIndex := List.replicate rowIndex ()
            indexRestore := []
            prefixCountdown := []
            outputReverse := data.outputReverse } = data := by
        cases data
        simp_all [DelimitedBinaryWords.encode]
      simpa [rowsTime, dataEq] using run
  | cons row rows induction =>
      let encodedTail := DelimitedBinaryWords.encode ⟨rows⟩ ++ tail
      let rank := DelimitedBinaryWordPrefixTrueCounts.count rowIndex row
      let afterRow : TapeData :=
        { data with
          input := encodedTail
          rowIndex := List.replicate (rowIndex + 1) ()
          indexRestore := []
          prefixCountdown := []
          outputReverse :=
            .delimiter :: List.replicate rank .unit ++ data.outputReverse }
      have first := oneRow_evalsInTime rowIndex row encodedTail data
        (by simpa [encodedTail, DelimitedBinaryWords.encode] using inputEq)
        indexEq restoreEq countdownEq
      have first' :
          EvalsToInTime (TM2.step program) (scanStartCfg data)
            (some (scanStartCfg afterRow)) (oneRowTime rowIndex row) := by
        simpa [afterRow, rank] using first
      have rest := induction (rowIndex + 1) afterRow rfl rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        (oneRowTime rowIndex row) (rowsTime (rowIndex + 1) rows)
        (scanStartCfg data) (scanStartCfg afterRow)
        (some (scanStartCfg
          { afterRow with
            input := tail
            rowIndex :=
              List.replicate (rowIndex + 1 + rows.length) ()
            indexRestore := []
            prefixCountdown := []
            outputReverse :=
              (UnaryFieldEncoderMachine.unaryFields
                (DelimitedBinaryWordPrefixTrueCounts.countsAux
                  (rowIndex + 1) rows)).reverse ++
                    afterRow.outputReverse }))
        first' rest
      have indexCountEq :
          rowIndex + 1 + rows.length = rowIndex + (rows.length + 1) := by
        omega
      rw [indexCountEq] at composed
      simpa [rowsTime, afterRow, rank,
        DelimitedBinaryWordPrefixTrueCounts.countsAux,
        UnaryFieldEncoderMachine.unaryFields_cons,
        UnaryFieldEncoderMachine.unaryField, List.reverse_append,
        List.append_assoc] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
