/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsExecution

/-! # Exact arithmetic for the Boolean square-row reshaper -/

namespace LeanTrominoes

namespace BoolSquareRowsMachine

open BoolSquareRows

theorem rootRoundsCost_formula (completed rounds : Nat) :
    rootRoundsCost completed rounds + 2 * completed =
      4 * (rounds + 1) * (2 * completed + rounds + 1) := by
  induction rounds generalizing completed with
  | zero =>
      simp [rootRoundsCost, lastRootRoundCost]
      ring
  | succ rounds induction =>
      calc
        rootRoundsCost completed (rounds + 1) + 2 * completed =
            (6 * completed + 4) +
              (rootRoundsCost (completed + 1) rounds +
                2 * (completed + 1)) + 2 * completed := by
                  simp [rootRoundsCost, nextRootRoundCost]
                  omega
        _ = (6 * completed + 4) +
              (4 * (rounds + 1) *
                (2 * (completed + 1) + rounds + 1)) +
              2 * completed := by rw [induction]
        _ = 4 * (rounds + 1 + 1) *
              (2 * completed + (rounds + 1) + 1) := by ring

theorem rootRoundsCost_zero (rounds : Nat) :
    rootRoundsCost 0 rounds = 4 * (rounds + 1) ^ 2 := by
  calc
    rootRoundsCost 0 rounds = 4 * (rounds + 1) * (rounds + 1) := by
      simpa using rootRoundsCost_formula 0 rounds
    _ = 4 * (rounds + 1) ^ 2 := by ring

theorem rowSequenceTime_formula (width furtherRows : Nat) :
    rowSequenceTime width furtherRows =
      furtherRows * (4 * width + 2) + 3 * width + 1 := by
  induction furtherRows with
  | zero => simp [rowSequenceTime]
  | succ furtherRows induction =>
      simp [rowSequenceTime, induction]
      ring

@[simp] theorem encodedRow_length (row : List Bool) :
    (encodedRow row).length = row.length + 2 := by
  simp [encodedRow]

theorem encodedRows_length_of_forall (rows : List (List Bool))
    (width : Nat) (lengths : rows.Forall fun row => row.length = width) :
    (encodedRows rows).length = rows.length * (width + 2) := by
  induction rows with
  | nil => simp [encodedRows]
  | cons row rows induction =>
      rw [List.forall_cons] at lengths
      change (encodedRow row ++ encodedRows rows).length =
        (row :: rows).length * (width + 2)
      rw [List.length_append, encodedRow_length, induction lengths.2,
        lengths.1]
      simp
      ring

@[simp] theorem encodedRows_input_length (input : BoolSquareRows.Input) :
    (encodedRows input.rows).length = input.side * (input.side + 2) :=
  by
    simpa using encodedRows_length_of_forall input.rows input.side
      (rows_forall_length input)

end BoolSquareRowsMachine
end LeanTrominoes
