/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupInput
import LeanTrominoes.LastTrueUnaryValueLookupRejectedFieldExecution
import LeanTrominoes.LastTrueUnaryValueLookupSelectedFieldExecution

/-! # Aligned bit/value recursion for last-true lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

/-- Exact cost of the aligned bit/value portion, including the row-end pop. -/
def bitsTime : Nat → List Bool → List Nat → Nat
  | _, [], _ => 1
  | candidate, false :: bits, value :: values =>
      bitsTime candidate bits values + (2 * value + 4)
  | candidate, true :: bits, value :: values =>
      bitsTime value bits values + (candidate + 3 * value + 5)
  | _, _ :: _, [] => 1

def bits_evalsInTime (candidate : Nat) (bits : List Bool)
    (values : List Nat) (rowsTail : List RowSymbol) (data : TapeData)
    (valid : RowValid bits values)
    (rowsEq : data.rows =
      bits.map .bit ++ .wordEnd :: rowsTail)
    (valuesEq : data.values =
      UnaryFieldEncoderMachine.unaryFields values)
    (candidateEq : data.candidate = List.replicate candidate ()) :
    EvalsToInTime machine.step (nextBitCfg data)
      (some (drainCandidateCfg
        { data with
          rows := rowsTail
          values := []
          valuesRestore :=
            (UnaryFieldEncoderMachine.unaryFields values).reverse ++
              data.valuesRestore
          candidate :=
            List.replicate (lookupAux candidate bits values) () }))
      (bitsTime candidate bits values) := by
  induction valid generalizing candidate data with
  | nil =>
      have finish := oneStep
        (step_nextBit_end data rowsTail (by simpa using rowsEq))
      simpa [bitsTime, lookupAux, UnaryFieldEncoderMachine.unaryFields,
        candidateEq, valuesEq] using finish
  | @cons bit value bits values valid induction =>
      let remainingRows : List RowSymbol :=
        bits.map .bit ++ .wordEnd :: rowsTail
      let remainingValues : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields values
      have rowsHead : data.rows = .bit bit :: remainingRows := by
        simpa [remainingRows] using rowsEq
      have valuesHead : data.values =
          UnaryFieldEncoderMachine.unaryField value ++ remainingValues := by
        simpa [remainingValues,
          UnaryFieldEncoderMachine.unaryFields_cons] using valuesEq
      cases bit with
      | false =>
          have opened := oneStep
            (step_nextBit_bit data false remainingRows rowsHead)
          have field := rejectedField_evalsInTime value remainingValues
            { data with rows := remainingRows } valuesHead
          let nextData : TapeData :=
            { data with
              rows := remainingRows
              values := remainingValues
              valuesRestore :=
                (UnaryFieldEncoderMachine.unaryField value).reverse ++
                  data.valuesRestore }
          have field' : EvalsToInTime machine.step
              (prepareValueCfg false { data with rows := remainingRows })
              (some (nextBitCfg nextData)) (2 * value + 3) := by
            simpa [nextData] using field
          have rest := induction candidate nextData rfl rfl
            (by simpa [nextData] using candidateEq)
          have throughField := EvalsToInTime.trans machine.step
            1 (2 * value + 3) _ _ _ opened field'
          have whole := EvalsToInTime.trans machine.step
            (2 * value + 3 + 1) (bitsTime candidate bits values)
            _ _ _ throughField rest
          convert whole using 1
          · simp [lookupAux, nextData,
              UnaryFieldEncoderMachine.unaryFields_cons,
              List.reverse_append, List.append_assoc]
          · simp [bitsTime]
      | true =>
          have opened := oneStep
            (step_nextBit_bit data true remainingRows rowsHead)
          have field := selectedField_evalsInTime value remainingValues
            (List.replicate candidate ()) { data with rows := remainingRows }
            valuesHead candidateEq
          let nextData : TapeData :=
            { data with
              rows := remainingRows
              values := remainingValues
              valuesRestore :=
                (UnaryFieldEncoderMachine.unaryField value).reverse ++
                  data.valuesRestore
              candidate := List.replicate value () }
          have field' : EvalsToInTime machine.step
              (prepareValueCfg true { data with rows := remainingRows })
              (some (nextBitCfg nextData)) (candidate + 3 * value + 4) := by
            simpa [nextData] using field
          have rest := induction value nextData rfl rfl rfl
          have throughField := EvalsToInTime.trans machine.step
            1 (candidate + 3 * value + 4) _ _ _ opened field'
          have whole := EvalsToInTime.trans machine.step
            (candidate + 3 * value + 4 + 1)
            (bitsTime value bits values)
            _ _ _ throughField rest
          convert whole using 1
          · simp [lookupAux, nextData,
              UnaryFieldEncoderMachine.unaryFields_cons,
              List.reverse_append, List.append_assoc]
          · simp [bitsTime]

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
