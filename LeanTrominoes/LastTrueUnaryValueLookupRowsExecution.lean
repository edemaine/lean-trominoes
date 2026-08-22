/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupOneRowExecution

/-! # Executing all rows of a last-true unary lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

def rowsTime : List (List Bool) → List Nat → Nat
  | [], _ => 0
  | row :: rows, values => rowsTime rows values + rowTime row values

def rows_evalsInTime (rows : List (List Bool)) (values : List Nat)
    (rowsTail : List RowSymbol) (data : TapeData)
    (valid : RowsValid values rows)
    (rowsEq : data.rows =
      DelimitedBinaryWords.encode ⟨rows⟩ ++ rowsTail)
    (valuesEq : data.values =
      UnaryFieldEncoderMachine.unaryFields values)
    (restoreEq : data.valuesRestore = [])
    (candidateEq : data.candidate = []) :
    EvalsToInTime machine.step (scanRowsCfg data)
      (some (scanRowsCfg
        { data with
          rows := rowsTail
          values := UnaryFieldEncoderMachine.unaryFields values
          valuesRestore := []
          candidate := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (lookups rows values)).reverse ++ data.outputReverse }))
      (rowsTime rows values) := by
  induction valid generalizing data with
  | nil =>
      have run := EvalsToInTime.refl machine.step (scanRowsCfg data)
      have dataEq :
          { data with
            rows := rowsTail
            values := UnaryFieldEncoderMachine.unaryFields values
            valuesRestore := []
            candidate := []
            outputReverse := data.outputReverse } = data := by
        cases data
        simp_all [DelimitedBinaryWords.encode]
      simpa [rowsTime, lookups, dataEq] using run
  | @cons row rows rowValid rest induction =>
      let encodedTail : List RowSymbol :=
        DelimitedBinaryWords.encode ⟨rows⟩ ++ rowsTail
      let nextData : TapeData :=
        { data with
          rows := encodedTail
          values := UnaryFieldEncoderMachine.unaryFields values
          valuesRestore := []
          candidate := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (lookup row values)).reverse ++ data.outputReverse }
      have first := row_evalsInTime row values encodedTail data rowValid
        (by simpa [encodedTail, DelimitedBinaryWords.encode,
          List.append_assoc] using rowsEq)
        valuesEq restoreEq candidateEq
      have first' : EvalsToInTime machine.step (scanRowsCfg data)
          (some (scanRowsCfg nextData)) (rowTime row values) := by
        simpa [nextData] using first
      have remaining := induction nextData rfl rfl rfl rfl
      have whole := EvalsToInTime.trans machine.step
        (rowTime row values) (rowsTime rows values)
        (scanRowsCfg data) (scanRowsCfg nextData)
        (some (scanRowsCfg
          { nextData with
            rows := rowsTail
            values := UnaryFieldEncoderMachine.unaryFields values
            valuesRestore := []
            candidate := []
            outputReverse :=
              (UnaryFieldEncoderMachine.unaryFields
                (lookups rows values)).reverse ++
                  nextData.outputReverse }))
        first' remaining
      simpa [rowsTime, lookups, nextData,
        UnaryFieldEncoderMachine.unaryFields_cons,
        List.reverse_append, List.append_assoc] using whole

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
