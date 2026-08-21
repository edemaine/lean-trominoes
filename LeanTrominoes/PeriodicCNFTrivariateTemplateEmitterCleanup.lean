/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterBoundarySteps
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterScan

/-! # Cleanup execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

def reverseOutput_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (word : List (Workspace Data)) (data : TapeData Data)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil firstSelected secondSelected positionSelected
          recipes ending data outputReverseEq)
      convert step using 1 <;> simp
  | cons workspace word induction =>
      let nextData : TapeData Data :=
        { data with
          outputReverse := word
          output := workspace :: data.output }
      have firstStep := oneStep
        (step_reverseOutput_cons firstSelected secondSelected positionSelected
          recipes ending data workspace word outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (reverseOutputCfg data)
        (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def clearFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (clearFirstCfg data)
      (some (clearSecondCfg { data with first := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearFirst_nil firstSelected secondSelected positionSelected
          recipes ending data firstEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with first := word }
      have firstStep := oneStep
        (step_clearFirst_cons firstSelected secondSelected positionSelected
          recipes ending data word firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (clearFirstCfg data)
        (clearFirstCfg nextData)
        (some (clearSecondCfg { nextData with first := [] }))
        firstStep rest
      simpa using composed

def clearSecond_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (word : List Unit) (data : TapeData Data)
    (secondEq : data.second = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (clearSecondCfg data)
      (some (clearProcessedCfg { data with second := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearSecond_nil firstSelected secondSelected positionSelected
          recipes ending data secondEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with second := word }
      have firstStep := oneStep
        (step_clearSecond_cons firstSelected secondSelected positionSelected
          recipes ending data word secondEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (clearSecondCfg data)
        (clearSecondCfg nextData)
        (some (clearProcessedCfg { nextData with second := [] }))
        firstStep rest
      simpa using composed

def clearProcessed_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (clearProcessedCfg data)
      (some (reverseOutputCfg { data with processed := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearProcessed_nil firstSelected secondSelected positionSelected
          recipes ending data processedEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with processed := word }
      have firstStep := oneStep
        (step_clearProcessed_cons firstSelected secondSelected
          positionSelected recipes ending data word processedEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step
          (program firstSelected secondSelected positionSelected
            recipes ending))
        1 (word.length + 1) (clearProcessedCfg data)
        (clearProcessedCfg nextData)
        (some (reverseOutputCfg { nextData with processed := [] }))
        firstStep rest
      simpa using composed

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
