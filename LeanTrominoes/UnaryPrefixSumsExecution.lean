/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsCleanupExecution
import LeanTrominoes.UnaryPrefixSumsListExecution
import LeanTrominoes.UnaryPrefixSumsReverseExecution

/-! # Complete execution of the unary prefix-sum machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

def outputWord (values : List Nat) : List Symbol :=
  UnaryFieldEncoderMachine.unaryFields (PrefixSums.starts values)

def totalTime (values : List Nat) : Nat :=
  (outputWord values).length + 1 +
    (values.sum + 1 + (1 + fieldsTime 0 values))

/-- Exact execution on a canonical sequence of unary input fields. -/
def execution (values : List Nat) :
    EvalsToInTime (TM2.step program)
      (readFieldCfg
        { input := UnaryFieldEncoderMachine.unaryFields values
          sum := []
          sumRestore := []
          outputReverse := []
          output := [] })
      (some (haltDataCfg
        { input := []
          sum := []
          sumRestore := []
          outputReverse := []
          output := outputWord values }))
      (totalTime values) := by
  let startData : TapeData :=
    { input := UnaryFieldEncoderMachine.unaryFields values
      sum := []
      sumRestore := []
      outputReverse := []
      output := [] }
  let scannedData : TapeData :=
    { input := []
      sum := List.replicate values.sum .unit
      sumRestore := []
      outputReverse := (outputWord values).reverse
      output := [] }
  let cleanedData : TapeData :=
    { scannedData with sum := [] }
  have fieldsRun := fields_evalsInTime 0 values [] startData
    (by simp [startData]) (by simp [startData]) (by simp [startData])
  have fieldsRun' :
      EvalsToInTime (TM2.step program) (readFieldCfg startData)
        (some (readFieldCfg scannedData)) (fieldsTime 0 values) := by
    simpa [startData, scannedData, outputWord, PrefixSums.starts] using
      fieldsRun
  have finishScan := FiniteBlockTransducer.oneStep
    (step_readField_nil scannedData rfl)
  have throughScan := EvalsToInTime.trans (TM2.step program)
    (fieldsTime 0 values) 1
    (readFieldCfg startData) (readFieldCfg scannedData)
    (some (clearSumCfg scannedData)) fieldsRun' finishScan
  have cleanupRun := clearSum_evalsInTime
    (List.replicate values.sum UnaryFieldEncoderMachine.Symbol.unit)
    scannedData rfl
  have cleanupRun' :
      EvalsToInTime (TM2.step program) (clearSumCfg scannedData)
        (some (reverseOutputCfg cleanedData)) (values.sum + 1) := by
    simpa [cleanedData] using cleanupRun
  have throughCleanup := EvalsToInTime.trans (TM2.step program)
    (1 + fieldsTime 0 values) (values.sum + 1)
    (readFieldCfg startData) (clearSumCfg scannedData)
    (some (reverseOutputCfg cleanedData)) throughScan cleanupRun'
  have reverseRun := reverseOutput_evalsInTime
    (outputWord values).reverse cleanedData rfl
  have reverseRun' :
      EvalsToInTime (TM2.step program) (reverseOutputCfg cleanedData)
        (some (haltDataCfg
          { input := []
            sum := []
            sumRestore := []
            outputReverse := []
            output := outputWord values }))
        ((outputWord values).length + 1) := by
    simpa [cleanedData, scannedData] using reverseRun
  have composed := EvalsToInTime.trans (TM2.step program)
    (values.sum + 1 + (1 + fieldsTime 0 values))
    ((outputWord values).length + 1)
    (readFieldCfg startData) (reverseOutputCfg cleanedData)
    (some (haltDataCfg
      { input := []
        sum := []
        sumRestore := []
        outputReverse := []
        output := outputWord values }))
    throughCleanup reverseRun'
  simpa [startData, totalTime] using composed

end UnaryPrefixSumsMachine
end LeanTrominoes
