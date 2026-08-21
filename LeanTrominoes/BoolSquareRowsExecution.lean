/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsPositiveExecution
import LeanTrominoes.BoolSquareRowsZeroExecution

/-! # Complete promised-square row-reshaper execution -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

open BoolSquareRows

def totalTime (input : BoolSquareRows.Input) : Nat :=
  if input.side = 0 then zeroTime else positiveExecutionTime input

theorem initList_eq_copyInputCfg (bits : List Bool) :
    initList machine bits =
      copyInputCfg ⟨bits, [], [], [], [], [], [], [], [], [], []⟩ := by
  unfold initList machine copyInputCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List OutputToken) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_evalsInTime (input : BoolSquareRows.Input) :
    EvalsToInTime (TM2.step program)
      (copyInputCfg
        ⟨input.bits, [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg
        (DelimitedBinaryWords.encode input.delimitedRows)))
      (totalTime input) := by
  by_cases sideZero : input.side = 0
  · have bitsNil := bits_eq_nil_of_side_eq_zero input sideZero
    have rowsNil : input.rows = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [rows_length, sideZero]
    simpa [totalTime, sideZero, bitsNil, rowsNil,
      Input.delimitedRows, DelimitedBinaryWords.encode] using zero_evalsInTime
  · have sidePos : 0 < input.side := Nat.pos_of_ne_zero sideZero
    simpa [totalTime, sideZero] using positive_evalsInTime input sidePos

/-- The fixed finite machine reshapes every promised Boolean square into its
canonical list of delimiter-separated rows. -/
def machine_outputsInTime (input : BoolSquareRows.Input) :
    TM2OutputsInTime machine input.bits
      (some (DelimitedBinaryWords.encode input.delimitedRows))
      (totalTime input) := by
  have run := machine_evalsInTime input
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind (TM2.step program))^[run.steps]
      (some (initList machine input.bits)) =
        some (haltList machine
          (DelimitedBinaryWords.encode input.delimitedRows))
  rw [initList_eq_copyInputCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end BoolSquareRowsMachine
end LeanTrominoes

end
