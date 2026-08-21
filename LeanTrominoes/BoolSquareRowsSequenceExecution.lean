/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsFullRowExecution
import LeanTrominoes.BoolSquareRowsRowRestoreExecution

/-! # Execution of a nonempty sequence of complete Boolean rows -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def encodedRow (row : List Bool) : List OutputToken :=
  .wordStart :: (row.map fun value => .bit value) ++ [.wordEnd]

def encodedRows (rows : List (List Bool)) : List OutputToken :=
  rows.flatMap encodedRow

/-- Time for a current row followed by the given number of further rows. -/
def rowSequenceTime (width : Nat) : Nat → Nat
  | 0 => 3 * width + 1
  | furtherRows + 1 =>
      rowSequenceTime width furtherRows +
        (width + 1 + (1 + 3 * width))

/-- Emit a current row and all subsequent equal-width rows.  The opening
delimiter for the current row is already on the reverse-output stack. -/
def rowSequence_evalsInTime (width : Nat) (widthPos : 0 < width)
    (row : List Bool) (furtherRows : List (List Bool))
    (rowLength : row.length = width)
    (furtherLengths : furtherRows.Forall fun next => next.length = width)
    (prior : List OutputToken) (data : TapeData)
    (sourceEq : data.source = (row :: furtherRows).flatten)
    (countdownEq : data.rowCountdown = List.replicate width ())
    (restoreEq : data.rowRestore = [])
    (outputReverseEq : data.outputReverse = .wordStart :: prior) :
    EvalsToInTime (TM2.step program) (emitBitCfg data)
      (some (clearRowRestoreCfg
        { data with
          source := []
          rowCountdown := []
          rowRestore := List.replicate width ()
          outputReverse := (encodedRows (row :: furtherRows)).reverse ++ prior }))
      (rowSequenceTime width furtherRows.length) := by
  induction furtherRows generalizing row prior data with
  | nil =>
      have rowNe : row ≠ [] := by
        intro rowEmpty
        subst row
        simp at rowLength
        omega
      let afterRow : TapeData :=
        { data with
          source := []
          rowCountdown := []
          rowRestore := List.replicate width ()
          outputReverse := (encodedRow row).reverse ++ prior }
      have emitted := fullRow_evalsInTime row [] rowNe data
        (by simpa using sourceEq)
        (by simpa [rowLength] using countdownEq)
      have finished := oneStep (step_finishRow_nil afterRow rfl)
      have whole := EvalsToInTime.trans (TM2.step program)
        (3 * row.length) 1
        (emitBitCfg data) (finishRowCfg afterRow)
        (some (clearRowRestoreCfg { afterRow with source := [] }))
        (by simpa [afterRow, rowLength, restoreEq, outputReverseEq,
          encodedRow, List.reverse_append, List.append_assoc] using emitted)
        finished
      convert whole using 1
      · simp [afterRow, encodedRows]
      · simp [rowSequenceTime, rowLength]
        omega
  | cons next remaining induction =>
      have rowNe : row ≠ [] := by
        intro rowEmpty
        subst row
        simp at rowLength
        omega
      rw [List.forall_cons] at furtherLengths
      have nextLength : next.length = width := furtherLengths.1
      have remainingLengths :
          remaining.Forall fun following => following.length = width :=
        furtherLengths.2
      have nextNe : next ≠ [] := by
        intro nextEmpty
        subst next
        simp at nextLength
        omega
      let nextBit := next.head nextNe
      let nextTail := next.tail
      have nextEq : nextBit :: nextTail = next :=
        List.cons_head_tail nextNe
      let afterRow : TapeData :=
        { data with
          source := (next :: remaining).flatten
          rowCountdown := []
          rowRestore := List.replicate width ()
          outputReverse := (encodedRow row).reverse ++ prior }
      have emitted := fullRow_evalsInTime row
        (next :: remaining).flatten rowNe data
        (by simpa using sourceEq)
        (by simpa [rowLength] using countdownEq)
      have finished := oneStep
        (step_finishRow_cons afterRow nextBit
          (nextTail ++ remaining.flatten) (by
            simp [afterRow, ← nextEq]))
      have throughFinish := EvalsToInTime.trans (TM2.step program)
        (3 * row.length) 1
        (emitBitCfg data) (finishRowCfg afterRow)
        (some (restoreRowCountCfg afterRow))
        (by simpa [afterRow, rowLength, restoreEq, outputReverseEq,
          encodedRow, List.reverse_append, List.append_assoc] using emitted)
        (by simpa [afterRow, ← nextEq] using finished)
      let nextData : TapeData :=
        { afterRow with
          rowCountdown := List.replicate width ()
          rowRestore := []
          outputReverse := .wordStart :: afterRow.outputReverse }
      have restored := restoreRowCount_evalsInTime
        (List.replicate width ()) afterRow rfl
      have throughRestore := EvalsToInTime.trans (TM2.step program)
        (1 + 3 * row.length) (width + 1)
        (emitBitCfg data) (restoreRowCountCfg afterRow)
        (some (emitBitCfg nextData))
        (by simpa using throughFinish)
        (by simpa [nextData, afterRow] using restored)
      have rest := induction next nextLength remainingLengths
        afterRow.outputReverse nextData
        (by simp [nextData, afterRow])
        (by simp [nextData]) (by simp [nextData])
        (by simp [nextData])
      have whole := EvalsToInTime.trans (TM2.step program)
        (width + 1 + (1 + 3 * row.length))
        (rowSequenceTime width remaining.length)
        (emitBitCfg data) (emitBitCfg nextData)
        (some (clearRowRestoreCfg
          { nextData with
            source := []
            rowCountdown := []
            rowRestore := List.replicate width ()
            outputReverse :=
              (encodedRows (next :: remaining)).reverse ++
                afterRow.outputReverse }))
        (by simpa using throughRestore) rest
      convert whole using 1
      · simp [nextData, afterRow, encodedRows, List.reverse_append,
          List.append_assoc]
      · simp [rowSequenceTime, rowLength]

end BoolSquareRowsMachine
end LeanTrominoes
