/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTimeArithmetic

/-! # Linear time bound for the Boolean square-row reshaper -/

namespace LeanTrominoes

namespace BoolSquareRowsMachine

open BoolSquareRows

theorem positiveExecutionTime_eq (input : BoolSquareRows.Input)
    (sidePos : 0 < input.side) :
    positiveExecutionTime input =
      11 * input.bits.length + 7 * input.side + 7 := by
  cases sideEq : input.side with
  | zero => simp [sideEq] at sidePos
  | succ additionalRounds =>
      have lengthEq :
          input.bits.length = (additionalRounds + 1) ^ 2 := by
        rw [length_eq_side_sq, sideEq]
      simp [positiveExecutionTime, positiveCountTime, rowsToHaltTime,
        startRowsTime, counterToRowsTime, rowSequenceTime_formula,
        rootRoundsCost_zero, sideEq, lengthEq, -encodedRows_eq_encode]
      ring

theorem side_le_bits_length (input : BoolSquareRows.Input)
    (sidePos : 0 < input.side) : input.side ≤ input.bits.length := by
  rw [length_eq_side_sq, pow_two]
  calc
    input.side = input.side * 1 := by simp
    _ ≤ input.side * input.side :=
      Nat.mul_le_mul_left input.side sidePos

theorem positiveExecutionTime_le (input : BoolSquareRows.Input)
    (sidePos : 0 < input.side) :
    positiveExecutionTime input ≤ 18 * input.bits.length + 7 := by
  rw [positiveExecutionTime_eq input sidePos]
  have sideBound := side_le_bits_length input sidePos
  omega

/-- The exact machine run is uniformly linear in the flat Boolean input. -/
theorem totalTime_le (input : BoolSquareRows.Input) :
    totalTime input ≤ 18 * input.bits.length + 12 := by
  by_cases sideZero : input.side = 0
  · simp [totalTime, sideZero, zeroTime]
  · have sidePos : 0 < input.side := Nat.pos_of_ne_zero sideZero
    rw [totalTime, if_neg sideZero]
    exact (positiveExecutionTime_le input sidePos).trans (by omega)

end BoolSquareRowsMachine
end LeanTrominoes
