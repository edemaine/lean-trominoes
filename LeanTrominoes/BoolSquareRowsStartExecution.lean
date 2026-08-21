/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsSequenceExecution

/-! # Starting a nonempty sequence of Boolean rows -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def startRowsTime (width furtherRows : Nat) : Nat :=
  rowSequenceTime width furtherRows + 1

/-- Open the first row and emit a nonempty list of complete equal-width rows. -/
def startRows_evalsInTime (width : Nat) (widthPos : 0 < width)
    (row : List Bool) (furtherRows : List (List Bool))
    (rowLength : row.length = width)
    (furtherLengths : furtherRows.Forall fun next => next.length = width)
    (data : TapeData)
    (sourceEq : data.source = (row :: furtherRows).flatten)
    (countdownEq : data.rowCountdown = List.replicate width ())
    (restoreEq : data.rowRestore = []) :
    EvalsToInTime (TM2.step program) (startRowsCfg data)
      (some (clearRowRestoreCfg
        { data with
          source := []
          rowCountdown := []
          rowRestore := List.replicate width ()
          outputReverse :=
            (encodedRows (row :: furtherRows)).reverse ++ data.outputReverse }))
      (startRowsTime width furtherRows.length) := by
  have rowNe : row ≠ [] := by
    intro rowEmpty
    subst row
    simp at rowLength
    omega
  let firstBit := row.head rowNe
  let rowTail := row.tail
  have rowEq : firstBit :: rowTail = row := List.cons_head_tail rowNe
  let started : TapeData :=
    { data with outputReverse := .wordStart :: data.outputReverse }
  have start := oneStep
    (step_startRows_cons data firstBit
      (rowTail ++ furtherRows.flatten) (by
        simp [sourceEq, ← rowEq]))
  have rows := rowSequence_evalsInTime width widthPos row furtherRows
    rowLength furtherLengths data.outputReverse started
    (by simp [started, sourceEq])
    (by simp [started, countdownEq])
    (by simp [started, restoreEq]) (by simp [started])
  have whole := EvalsToInTime.trans (TM2.step program)
    1 (rowSequenceTime width furtherRows.length)
    (startRowsCfg data) (emitBitCfg started)
    (some (clearRowRestoreCfg
      { started with
        source := []
        rowCountdown := []
        rowRestore := List.replicate width ()
        outputReverse :=
          (encodedRows (row :: furtherRows)).reverse ++
            data.outputReverse }))
    (by simpa [started, sourceEq, ← rowEq] using start) rows
  convert whole using 1
  · rfl

end BoolSquareRowsMachine
end LeanTrominoes
