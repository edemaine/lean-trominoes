/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsReverseOutputExecution
import LeanTrominoes.BoolSquareRowsRowCleanupExecution
import LeanTrominoes.BoolSquareRowsStartExecution

/-! # Complete emission of nonempty Boolean rows -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

def rowsToHaltTime (width furtherRows : Nat) (outputLength : Nat) : Nat :=
  outputLength + 1 + (width + 1 + startRowsTime width furtherRows)

/-- Emit all rows, clear the final row counter, and reverse the token stream
onto the designated output stack. -/
def rowsToHalt_evalsInTime (width : Nat) (widthPos : 0 < width)
    (row : List Bool) (furtherRows : List (List Bool))
    (rowLength : row.length = width)
    (furtherLengths : furtherRows.Forall fun next => next.length = width) :
    EvalsToInTime (TM2.step program)
      (startRowsCfg
        ⟨[], [], [], [], [], [], (row :: furtherRows).flatten,
          List.replicate width (), [], [], []⟩)
      (some (haltCfg (encodedRows (row :: furtherRows))))
      (rowsToHaltTime width furtherRows.length
        (encodedRows (row :: furtherRows)).length) := by
  let rows := row :: furtherRows
  let output := encodedRows rows
  let afterRows : TapeData :=
    ⟨[], [], [], [], [], [], [], [],
      List.replicate width (), output.reverse, []⟩
  have emitted := startRows_evalsInTime width widthPos row furtherRows
    rowLength furtherLengths
    ⟨[], [], [], [], [], [], rows.flatten,
      List.replicate width (), [], [], []⟩ rfl rfl rfl
  have cleared := clearRowRestore_evalsInTime
    (List.replicate width ()) afterRows rfl
  have throughClear := EvalsToInTime.trans (TM2.step program)
    (startRowsTime width furtherRows.length) (width + 1)
    (startRowsCfg
      ⟨[], [], [], [], [], [], rows.flatten,
        List.replicate width (), [], [], []⟩)
    (clearRowRestoreCfg afterRows)
    (some (reverseOutputCfg
      ⟨[], [], [], [], [], [], [], [], [], output.reverse, []⟩))
    (by simpa [rows, output, afterRows] using emitted)
    (by simpa [afterRows, output] using cleared)
  have reversed := reverseOutput_evalsInTime output.reverse []
  have whole := EvalsToInTime.trans (TM2.step program)
    (width + 1 + startRowsTime width furtherRows.length)
    (output.reverse.length + 1)
    (startRowsCfg
      ⟨[], [], [], [], [], [], rows.flatten,
        List.replicate width (), [], [], []⟩)
    (reverseOutputCfg
      ⟨[], [], [], [], [], [], [], [], [], output.reverse, []⟩)
    (some (haltCfg output)) throughClear (by simpa using reversed)
  convert whole using 1
  simp [rowsToHaltTime, output, rows]

end BoolSquareRowsMachine
end LeanTrominoes
