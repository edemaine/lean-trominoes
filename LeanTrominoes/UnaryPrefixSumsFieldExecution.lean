/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsEmitStartExecution
import LeanTrominoes.UnaryPrefixSumsFieldScanExecution

/-! # Executing one unary prefix-sum field -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

@[simp] theorem unitSymbols_replicate (count : Nat) :
    unitSymbols (List.replicate count ()) =
      List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  simp [unitSymbols]

theorem accumulated_units (start value : Nat) :
    List.replicate value UnaryFieldEncoderMachine.Symbol.unit ++
        UnaryFieldEncoderMachine.Symbol.unit ::
          List.replicate start UnaryFieldEncoderMachine.Symbol.unit =
      List.replicate (start + value.succ)
        UnaryFieldEncoderMachine.Symbol.unit := by
  rw [← List.replicate_succ]
  rw [← List.replicate_add]
  congr 1
  omega

/-- Read one unary field, emit its current block start, and add its size to
the cumulative sum. -/
def field_evalsInTime (start value : Nat) (tail : List Symbol)
    (data : TapeData)
    (inputEq : data.input =
      UnaryFieldEncoderMachine.unaryField value ++ tail)
    (sumEq : data.sum = List.replicate start .unit)
    (restoreEq : data.sumRestore = []) :
    EvalsToInTime (TM2.step program) (readFieldCfg data)
      (some (readFieldCfg
        { data with
          input := tail
          sum := List.replicate (start + value) .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }))
      (2 * start + value + 4) := by
  cases value with
  | zero =>
      let afterRead : TapeData := { data with input := tail }
      let afterEmit : TapeData :=
        { data with
          input := tail
          sum := List.replicate start .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }
      have readRun := FiniteBlockTransducer.oneStep
        (step_readField_cons data .delimiter tail (by
          simpa [UnaryFieldEncoderMachine.unaryField] using inputEq))
      have emitRun := emitStart_evalsInTime .delimiter start afterRead
        (by simpa [afterRead] using sumEq)
        (by simpa [afterRead] using restoreEq)
      have emitRun' :
          EvalsToInTime (TM2.step program)
            (copySumCfg .delimiter afterRead)
            (some (consumeSavedCfg .delimiter afterEmit))
            (2 * start + 2) := by
        simpa [afterRead, afterEmit] using emitRun
      have consumeRun := FiniteBlockTransducer.oneStep
        (step_consumeSaved_delimiter afterEmit)
      have throughEmit := EvalsToInTime.trans (TM2.step program)
        1 (2 * start + 2)
        (readFieldCfg data) (copySumCfg .delimiter afterRead)
        (some (consumeSavedCfg .delimiter afterEmit))
        readRun emitRun'
      have composed := EvalsToInTime.trans (TM2.step program)
        (2 * start + 2 + 1) 1
        (readFieldCfg data) (consumeSavedCfg .delimiter afterEmit)
        (some (readFieldCfg afterEmit))
        throughEmit consumeRun
      convert composed using 1 <;> simp [afterEmit]
      omega
  | succ value =>
      let remainingInput : List Symbol :=
        List.replicate value .unit ++ .delimiter :: tail
      let afterRead : TapeData := { data with input := remainingInput }
      let afterEmit : TapeData :=
        { data with
          input := remainingInput
          sum := List.replicate start .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }
      let afterConsume : TapeData :=
        { afterEmit with sum := .unit :: afterEmit.sum }
      let afterField : TapeData :=
        { data with
          input := tail
          sum := List.replicate (start + value.succ) .unit
          sumRestore := []
          outputReverse :=
            .delimiter :: List.replicate start .unit ++
              data.outputReverse }
      have readRun := FiniteBlockTransducer.oneStep
        (step_readField_cons data .unit remainingInput (by
          simpa [remainingInput, UnaryFieldEncoderMachine.unaryField,
            List.replicate_succ] using inputEq))
      have emitRun := emitStart_evalsInTime .unit start afterRead
        (by simpa [afterRead] using sumEq)
        (by simpa [afterRead] using restoreEq)
      have emitRun' :
          EvalsToInTime (TM2.step program) (copySumCfg .unit afterRead)
            (some (consumeSavedCfg .unit afterEmit))
            (2 * start + 2) := by
        simpa [afterRead, afterEmit] using emitRun
      have consumeRun := FiniteBlockTransducer.oneStep
        (step_consumeSaved_unit afterEmit)
      have scanRun := scanUnits_evalsInTime
        (List.replicate value ()) tail afterConsume (by
          simp [afterConsume, afterEmit, remainingInput, unitSymbols])
      have scanRun' :
          EvalsToInTime (TM2.step program) (scanFieldCfg afterConsume)
            (some (readFieldCfg afterField)) (value + 1) := by
        simpa [afterConsume, afterEmit, afterField, remainingInput,
          accumulated_units] using scanRun
      have throughEmit := EvalsToInTime.trans (TM2.step program)
        1 (2 * start + 2)
        (readFieldCfg data) (copySumCfg .unit afterRead)
        (some (consumeSavedCfg .unit afterEmit))
        readRun emitRun'
      have throughConsume := EvalsToInTime.trans (TM2.step program)
        (2 * start + 2 + 1) 1
        (readFieldCfg data) (consumeSavedCfg .unit afterEmit)
        (some (scanFieldCfg afterConsume))
        throughEmit consumeRun
      have composed := EvalsToInTime.trans (TM2.step program)
        (1 + (2 * start + 2 + 1)) (value + 1)
        (readFieldCfg data) (scanFieldCfg afterConsume)
        (some (readFieldCfg afterField))
        throughConsume scanRun'
      convert composed using 1
      omega

end UnaryPrefixSumsMachine
end LeanTrominoes
