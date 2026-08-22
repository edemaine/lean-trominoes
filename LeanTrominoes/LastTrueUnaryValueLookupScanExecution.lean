/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupParsing
import LeanTrominoes.LastTrueUnaryValueLookupRowsExecution

/-! # Complete parsing and scanning for last-true unary lookup -/

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

/-- Exact cost through parsing, row evaluation, and value cleanup. -/
def scanTime (input : Input) : Nat :=
  (UnaryFieldEncoderMachine.unaryFields input.values).length + 1 + 1 +
    rowsTime input.rows input.values +
      parseTime
        (DelimitedBinaryWords.encode ⟨input.rows⟩)
        (UnaryFieldEncoderMachine.unaryFields input.values)

def scan_evalsInTime (input : Input) :
    EvalsToInTime machine.step
      (scanLeftCfg ⟨encode input, [], [], [], [], [], [], [], []⟩)
      (some (reverseOutputCfg
        ⟨[], [], [], [], [], [], [],
          (outputEncoding input).reverse, []⟩))
      (scanTime input) := by
  let rows := DelimitedBinaryWords.encode ⟨input.rows⟩
  let values := UnaryFieldEncoderMachine.unaryFields input.values
  let parsedData : TapeData :=
    ⟨[], [], rows, [], values, [], [], [], []⟩
  let processedData : TapeData :=
    ⟨[], [], [], [], values, [], [],
      (outputEncoding input).reverse, []⟩
  let cleanedData : TapeData :=
    ⟨[], [], [], [], [], [], [],
      (outputEncoding input).reverse, []⟩
  have parseRun := parsing_evalsInTime rows values
  have parseRun' : EvalsToInTime machine.step
      (scanLeftCfg ⟨encode input, [], [], [], [], [], [], [], []⟩)
      (some (scanRowsCfg parsedData)) (parseTime rows values) := by
    simpa [parsedData, rows, values, encode,
      SeparatedProductEncoding.encode] using parseRun
  have rowsRun := rows_evalsInTime input.rows input.values []
    parsedData input.valid
    (by simp [parsedData, rows])
    (by simp [parsedData, values])
    (by simp [parsedData])
    (by simp [parsedData])
  have rowsRun' : EvalsToInTime machine.step (scanRowsCfg parsedData)
      (some (scanRowsCfg processedData))
      (rowsTime input.rows input.values) := by
    simpa [parsedData, processedData, values, outputEncoding] using rowsRun
  have throughRows := EvalsToInTime.trans machine.step
    (parseTime rows values) (rowsTime input.rows input.values)
    _ _ _ parseRun' rowsRun'
  have finishedRows := oneStep (step_scanRows_nil processedData rfl)
  have throughFinish := EvalsToInTime.trans machine.step
    (rowsTime input.rows input.values + parseTime rows values) 1
    _ _ _ throughRows (by simpa [processedData] using finishedRows)
  have cleared := clearValues_evalsInTime values processedData rfl
  have cleared' : EvalsToInTime machine.step (clearValuesCfg processedData)
      (some (reverseOutputCfg cleanedData)) (values.length + 1) := by
    simpa [processedData, cleanedData] using cleared
  have whole := EvalsToInTime.trans machine.step
    (1 + (rowsTime input.rows input.values + parseTime rows values))
    (values.length + 1) _ _ _ throughFinish cleared'
  convert whole using 1
  simp [scanTime, rows, values]
  omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
