/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCounterToRowsExecution
import LeanTrominoes.BoolSquareRowsInput
import LeanTrominoes.BoolSquareRowsPositiveCountExecution
import LeanTrominoes.BoolSquareRowsToHaltExecution

/-! # Complete execution on positive Boolean squares -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

open BoolSquareRows

def positiveExecutionTime (input : BoolSquareRows.Input) : Nat :=
  rowsToHaltTime input.side (input.side - 1)
      (encodedRows input.rows).length +
    (counterToRowsTime []
        (List.replicate (2 * (input.side - 1) + 1) ())
        (List.replicate input.side ()) input.bits.reverse +
      positiveCountTime input.bits (input.side - 1))

/-- The complete finite machine emits canonical delimiter-separated rows for
every promised square of positive side length. -/
def positive_evalsInTime (input : BoolSquareRows.Input)
    (sidePos : 0 < input.side) :
    EvalsToInTime (TM2.step program)
      (copyInputCfg
        ⟨input.bits, [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg
        (DelimitedBinaryWords.encode input.delimitedRows)))
      (positiveExecutionTime input) := by
  cases sideEq : input.side with
  | zero => simp [sideEq] at sidePos
  | succ additionalRounds =>
      have lengthEq :
          input.bits.length = (additionalRounds + 1) ^ 2 := by
        rw [length_eq_side_sq, sideEq]
      have counted := positiveCount_evalsInTime input.bits
        additionalRounds lengthEq
      let countedData : TapeData :=
        ⟨[], input.bits.reverse, [], [],
          List.replicate (2 * additionalRounds + 1) (),
          List.replicate (additionalRounds + 1) (),
          [], [], [], [], []⟩
      have cleaned := counterToRows_evalsInTime []
        (List.replicate (2 * additionalRounds + 1) ())
        (List.replicate (additionalRounds + 1) ())
        input.bits.reverse countedData rfl rfl rfl rfl
      let rowsData : TapeData :=
        ⟨[], [], [], [], [], [], input.bits,
          List.replicate (additionalRounds + 1) (), [], [], []⟩
      have throughRows := EvalsToInTime.trans (TM2.step program)
        (positiveCountTime input.bits additionalRounds)
        (counterToRowsTime []
          (List.replicate (2 * additionalRounds + 1) ())
          (List.replicate (additionalRounds + 1) ()) input.bits.reverse)
        (copyInputCfg
          ⟨input.bits, [], [], [], [], [], [], [], [], [], []⟩)
        (clearOddCfg countedData) (some (startRowsCfg rowsData))
        (by simpa [countedData] using counted)
        (by simpa [countedData, rowsData] using cleaned)
      cases rowsEq : input.rows with
      | nil =>
          have rowsLength := rows_length input
          rw [rowsEq, sideEq] at rowsLength
          simp at rowsLength
      | cons row furtherRows =>
          have lengths := rows_forall_length input
          rw [rowsEq, List.forall_cons] at lengths
          have rowLength : row.length = additionalRounds + 1 := by
            simpa [sideEq] using lengths.1
          have furtherLengths :
              furtherRows.Forall fun next =>
                next.length = additionalRounds + 1 := by
            simpa [sideEq] using lengths.2
          have furtherLength : furtherRows.length = additionalRounds := by
            have totalLength := rows_length input
            rw [rowsEq, sideEq] at totalLength
            simpa using totalLength
          have sourceRows :
              input.bits = row ++ furtherRows.flatten := by
            rw [← rows_flatten input, rowsEq]
            simp
          have emitted := rowsToHalt_evalsInTime
            (additionalRounds + 1) (by omega) row furtherRows
            rowLength furtherLengths
          have emitted' : EvalsToInTime (TM2.step program)
              (startRowsCfg rowsData)
              (some (haltCfg (encodedRows input.rows)))
              (rowsToHaltTime (additionalRounds + 1) furtherRows.length
                (encodedRows input.rows).length) := by
            simpa [rowsData, rowsEq, sourceRows] using emitted
          have whole := EvalsToInTime.trans (TM2.step program)
            (counterToRowsTime []
                (List.replicate (2 * additionalRounds + 1) ())
                (List.replicate (additionalRounds + 1) ())
                input.bits.reverse +
              positiveCountTime input.bits additionalRounds)
            (rowsToHaltTime (additionalRounds + 1) furtherRows.length
              (encodedRows input.rows).length)
            (copyInputCfg
              ⟨input.bits, [], [], [], [], [], [], [], [], [], []⟩)
            (startRowsCfg rowsData)
            (some (haltCfg (encodedRows input.rows)))
            throughRows emitted'
          rw [encodedRows_eq_encode] at whole
          convert whole using 1
          simp [positiveExecutionTime, sideEq, furtherLength]

end BoolSquareRowsMachine
end LeanTrominoes
