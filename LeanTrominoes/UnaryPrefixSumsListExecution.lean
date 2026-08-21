/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.PrefixSums
import LeanTrominoes.UnaryPrefixSumsFieldExecution

/-! # Executing a list of unary prefix-sum fields -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

def fieldsTime : Nat → List Nat → Nat
  | _, [] => 0
  | start, value :: values =>
      fieldsTime (start + value) values + (2 * start + value + 4)

/-- Process every input field, maintaining the cumulative sum and accumulating
the reverse encoding of all block starts. -/
def fields_evalsInTime (start : Nat) (values : List Nat)
    (tail : List Symbol) (data : TapeData)
    (inputEq : data.input =
      UnaryFieldEncoderMachine.unaryFields values ++ tail)
    (sumEq : data.sum = List.replicate start .unit)
    (restoreEq : data.sumRestore = []) :
    EvalsToInTime (TM2.step program) (readFieldCfg data)
      (some (readFieldCfg
        { data with
          input := tail
          sum := List.replicate (start + values.sum) .unit
          sumRestore := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (PrefixSums.startsAux start values)).reverse ++
                data.outputReverse }))
      (fieldsTime start values) := by
  induction values generalizing start data with
  | nil =>
      rcases data with
        ⟨input, sum, sumRestore, outputReverse, output⟩
      change input =
        UnaryFieldEncoderMachine.unaryFields [] ++ tail at inputEq
      change sum = List.replicate start .unit at sumEq
      change sumRestore = [] at restoreEq
      simp only [UnaryFieldEncoderMachine.unaryFields_nil,
        List.nil_append] at inputEq
      subst input
      subst sum
      subst sumRestore
      have zero := UnaryFieldEncoderMachine.zeroSteps
        (transition := TM2.step program)
        (readFieldCfg
          { input := tail
            sum := List.replicate start .unit
            sumRestore := []
            outputReverse := outputReverse
            output := output })
      simpa [fieldsTime, PrefixSums.startsAux,
        UnaryFieldEncoderMachine.unaryFields] using zero
  | cons value values induction =>
      let remaining : List Symbol :=
        UnaryFieldEncoderMachine.unaryFields values ++ tail
      let nextData : TapeData :=
        { data with
          input := remaining
          sum := List.replicate (start + value) .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }
      have fieldInputEq : data.input =
          UnaryFieldEncoderMachine.unaryField value ++ remaining := by
        simpa [remaining, UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using inputEq
      have first := field_evalsInTime start value remaining data
        fieldInputEq sumEq restoreEq
      have rest := induction (start + value) nextData rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        (2 * start + value + 4) (fieldsTime (start + value) values)
        (readFieldCfg data) (readFieldCfg nextData)
        (some (readFieldCfg
          { nextData with
            input := tail
            sum := List.replicate
              (start + value + values.sum) .unit
            sumRestore := []
            outputReverse :=
              (UnaryFieldEncoderMachine.unaryFields
                (PrefixSums.startsAux (start + value) values)).reverse ++
                  nextData.outputReverse }))
        first rest
      convert composed using 1 <;>
        simp [nextData, fieldsTime, PrefixSums.startsAux,
          UnaryFieldEncoderMachine.unaryFields_cons,
          UnaryFieldEncoderMachine.unaryField, List.reverse_append,
          List.append_assoc, Nat.add_assoc]

end UnaryPrefixSumsMachine
end LeanTrominoes
