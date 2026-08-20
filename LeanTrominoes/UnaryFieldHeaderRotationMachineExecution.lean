/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldHeaderRotationMachine

/-! # Exact phase executions for unary strip-header rotation -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryFieldHeaderRotationMachine

open UnaryFieldEncoderMachine

/-- Unary units before the first delimiter. -/
def fieldUnits : List Symbol → List Symbol
  | [] => []
  | .unit :: symbols => .unit :: fieldUnits symbols
  | .delimiter :: _ => []

/-- Suffix after the first delimiter, or the empty list when none occurs. -/
def afterField : List Symbol → List Symbol
  | [] => []
  | .unit :: symbols => afterField symbols
  | .delimiter :: symbols => symbols

/-- Canonical delimiter-terminated form of the first possibly malformed
field. -/
def normalizedField (symbols : List Symbol) : List Symbol :=
  fieldUnits symbols ++ [.delimiter]

def fieldScanTime : List Symbol → Nat
  | [] => 1
  | .unit :: symbols => 1 + fieldScanTime symbols
  | .delimiter :: _ => 1

@[simp] theorem consumeFieldAux_eq_fieldUnits
    (initial : Nat) (symbols : List Symbol) :
    UnaryFieldHeaderRotation.consumeFieldAux initial symbols =
      (initial + (fieldUnits symbols).length, afterField symbols) := by
  induction symbols generalizing initial with
  | nil => simp [UnaryFieldHeaderRotation.consumeFieldAux,
      fieldUnits, afterField]
  | cons symbol symbols induction =>
      cases symbol with
      | unit =>
          simp only [UnaryFieldHeaderRotation.consumeFieldAux, fieldUnits,
            afterField, List.length_cons]
          rw [induction]
          congr 1
          omega
      | delimiter =>
          simp [UnaryFieldHeaderRotation.consumeFieldAux,
            fieldUnits, afterField]

@[simp] theorem consumeField_eq_fieldUnits (symbols : List Symbol) :
    UnaryFieldHeaderRotation.consumeField symbols =
      ((fieldUnits symbols).length, afterField symbols) := by
  simp [UnaryFieldHeaderRotation.consumeField]

theorem fieldUnits_eq_replicate (symbols : List Symbol) :
    ∃ count : Nat, fieldUnits symbols = List.replicate count .unit := by
  induction symbols with
  | nil => exact ⟨0, rfl⟩
  | cons symbol symbols induction =>
      cases symbol with
      | unit =>
          obtain ⟨count, induction⟩ := induction
          exact ⟨count + 1, by
            simp [fieldUnits, induction, List.replicate_succ]⟩
      | delimiter => exact ⟨0, rfl⟩

@[simp] theorem fieldUnits_reverse (symbols : List Symbol) :
    (fieldUnits symbols).reverse = fieldUnits symbols := by
  obtain ⟨count, equality⟩ := fieldUnits_eq_replicate symbols
  simp [equality]

@[simp] theorem unaryField_fieldUnits_length (symbols : List Symbol) :
    unaryField (fieldUnits symbols).length = normalizedField symbols := by
  obtain ⟨count, equality⟩ := fieldUnits_eq_replicate symbols
  simp [UnaryFieldEncoderMachine.unaryField, normalizedField, equality]

theorem rotateFirstFieldAfterTwo_eq_normalizedFields
    (symbols : List Symbol) :
    UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo symbols =
      let afterFirst := afterField symbols
      let afterSecond := afterField afterFirst
      let suffix := afterField afterSecond
      normalizedField afterFirst ++ normalizedField afterSecond ++
        normalizedField symbols ++ suffix := by
  simp only [UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo,
    consumeField_eq_fieldUnits]
  simp [List.append_assoc]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

def scanFirst_evalsInTime (symbols : List Symbol) (data : TapeData)
    (inputEq : data.input = symbols) :
    EvalsToInTime (TM2.step program) (scanFirstCfg data)
      (some (scanSecondCfg
        { data with
          input := afterField symbols
          firstReverse :=
            (fieldUnits symbols).reverse ++ data.firstReverse }))
      (fieldScanTime symbols) := by
  induction symbols generalizing data with
  | nil =>
      have step := oneStep (step_scanFirst_nil data inputEq)
      convert step using 1 <;>
        simp [fieldUnits, afterField, fieldScanTime]
  | cons symbol symbols induction =>
      cases symbol with
      | unit =>
          let nextData :=
            { data with
              input := symbols
              firstReverse := .unit :: data.firstReverse }
          have first := oneStep (step_scanFirst_unit data symbols inputEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (fieldScanTime symbols)
            (scanFirstCfg data) (scanFirstCfg nextData)
            (some (scanSecondCfg
              { nextData with
                input := afterField symbols
                firstReverse :=
                  (fieldUnits symbols).reverse ++ nextData.firstReverse }))
            first rest
          convert composed using 1
          · simp [fieldUnits, afterField, nextData, List.reverse_cons,
              List.append_assoc]
          · simp only [fieldScanTime]
            omega
      | delimiter =>
          have step := oneStep
            (step_scanFirst_delimiter data symbols inputEq)
          convert step using 1 <;>
            simp [fieldUnits, afterField, fieldScanTime]

def scanSecond_evalsInTime (symbols : List Symbol) (data : TapeData)
    (inputEq : data.input = symbols) :
    EvalsToInTime (TM2.step program) (scanSecondCfg data)
      (some (scanThirdCfg
        { data with
          input := afterField symbols
          outputReverse :=
            (normalizedField symbols).reverse ++ data.outputReverse }))
      (fieldScanTime symbols) := by
  induction symbols generalizing data with
  | nil =>
      have step := oneStep (step_scanSecond_nil data inputEq)
      convert step using 1 <;>
        simp [normalizedField, fieldUnits, afterField, fieldScanTime]
  | cons symbol symbols induction =>
      cases symbol with
      | unit =>
          let nextData :=
            { data with
              input := symbols
              outputReverse := .unit :: data.outputReverse }
          have first := oneStep (step_scanSecond_unit data symbols inputEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (fieldScanTime symbols)
            (scanSecondCfg data) (scanSecondCfg nextData)
            (some (scanThirdCfg
              { nextData with
                input := afterField symbols
                outputReverse :=
                  (normalizedField symbols).reverse ++
                    nextData.outputReverse }))
            first rest
          convert composed using 1
          · simp [normalizedField, fieldUnits, afterField, nextData,
              List.reverse_cons, List.reverse_append, List.append_assoc]
          · simp only [fieldScanTime]
            omega
      | delimiter =>
          have step := oneStep
            (step_scanSecond_delimiter data symbols inputEq)
          convert step using 1 <;>
            simp [normalizedField, fieldUnits, afterField, fieldScanTime]

def scanThird_evalsInTime (symbols : List Symbol) (data : TapeData)
    (inputEq : data.input = symbols) :
    EvalsToInTime (TM2.step program) (scanThirdCfg data)
      (some (emitFirstCfg
        { data with
          input := afterField symbols
          outputReverse :=
            (normalizedField symbols).reverse ++ data.outputReverse }))
      (fieldScanTime symbols) := by
  induction symbols generalizing data with
  | nil =>
      have step := oneStep (step_scanThird_nil data inputEq)
      convert step using 1 <;>
        simp [normalizedField, fieldUnits, afterField, fieldScanTime]
  | cons symbol symbols induction =>
      cases symbol with
      | unit =>
          let nextData :=
            { data with
              input := symbols
              outputReverse := .unit :: data.outputReverse }
          have first := oneStep (step_scanThird_unit data symbols inputEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (fieldScanTime symbols)
            (scanThirdCfg data) (scanThirdCfg nextData)
            (some (emitFirstCfg
              { nextData with
                input := afterField symbols
                outputReverse :=
                  (normalizedField symbols).reverse ++
                    nextData.outputReverse }))
            first rest
          convert composed using 1
          · simp [normalizedField, fieldUnits, afterField, nextData,
              List.reverse_cons, List.reverse_append, List.append_assoc]
          · simp only [fieldScanTime]
            omega
      | delimiter =>
          have step := oneStep
            (step_scanThird_delimiter data symbols inputEq)
          convert step using 1 <;>
            simp [normalizedField, fieldUnits, afterField, fieldScanTime]

def emitFirst_evalsInTime (word : List Symbol) (data : TapeData)
    (firstEq : data.firstReverse = word) :
    EvalsToInTime (TM2.step program) (emitFirstCfg data)
      (some (copySuffixCfg
        { data with
          firstReverse := []
          outputReverse :=
            .delimiter :: word.reverse ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitFirst_nil data firstEq)
      convert step using 1 <;> simp
  | cons symbol word induction =>
      let nextData :=
        { data with
          firstReverse := word
          outputReverse := symbol :: data.outputReverse }
      have first := oneStep
        (step_emitFirst_cons data symbol word firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (emitFirstCfg data) (emitFirstCfg nextData)
        (some (copySuffixCfg
          { nextData with
            firstReverse := []
            outputReverse :=
              .delimiter :: word.reverse ++ nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def copySuffix_evalsInTime (symbols : List Symbol) (data : TapeData)
    (inputEq : data.input = symbols) :
    EvalsToInTime (TM2.step program) (copySuffixCfg data)
      (some (reverseOutputCfg
        { data with
          input := []
          outputReverse := symbols.reverse ++ data.outputReverse }))
      (symbols.length + 1) := by
  induction symbols generalizing data with
  | nil =>
      have step := oneStep (step_copySuffix_nil data inputEq)
      convert step using 1 <;> simp
  | cons symbol symbols induction =>
      let nextData :=
        { data with
          input := symbols
          outputReverse := symbol :: data.outputReverse }
      have first := oneStep
        (step_copySuffix_cons data symbol symbols inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (symbols.length + 1)
        (copySuffixCfg data) (copySuffixCfg nextData)
        (some (reverseOutputCfg
          { nextData with
            input := []
            outputReverse :=
              symbols.reverse ++ nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def reverseOutput_evalsInTime (word : List Symbol) (data : TapeData)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step program) (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_reverseOutput_nil data outputReverseEq)
      convert step using 1 <;> simp
  | cons symbol word induction =>
      let nextData :=
        { data with
          outputReverse := word
          output := symbol :: data.output }
      have first := oneStep
        (step_reverseOutput_cons data symbol word outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (reverseOutputCfg data) (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end UnaryFieldHeaderRotationMachine
end LeanTrominoes
