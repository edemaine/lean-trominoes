/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupValueSteps

/-! # Output and restoration steps of last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open Turing

attribute [local simp] initialState setUnary setCandidate clearUnary
  clearCandidateState unaryIsNone candidateIsNone unaryState storedUnary

theorem step_drainCandidate_cons (data : TapeData)
    (remaining : List Unit)
    (candidateEq : data.candidate = () :: remaining) :
    machine.step (drainCandidateCfg data) =
      some (pushOutputUnitCfg { data with candidate := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change candidate = _ at candidateEq
  subst candidate
  simp [TM2.step, program, drainCandidateCfg, pushOutputUnitCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_drainCandidate_nil (data : TapeData)
    (candidateEq : data.candidate = []) :
    machine.step (drainCandidateCfg data) =
      some (emitDelimiterCfg { data with candidate := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change candidate = [] at candidateEq
  subst candidate
  simp [TM2.step, program, drainCandidateCfg, emitDelimiterCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_pushOutputUnit (data : TapeData) :
    machine.step (pushOutputUnitCfg data) =
      some (drainCandidateCfg
        { data with outputReverse := .unit :: data.outputReverse }) := by
  simp [TM2.step, program, pushOutputUnitCfg, drainCandidateCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_emitDelimiter (data : TapeData) :
    machine.step (emitDelimiterCfg data) =
      some (restoreValuesCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  simp [TM2.step, program, emitDelimiterCfg, restoreValuesCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_restoreValues_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (restoreEq : data.valuesRestore = symbol :: remaining) :
    machine.step (restoreValuesCfg data) =
      some (pushRestoredValueCfg symbol
        { data with valuesRestore := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change valuesRestore = _ at restoreEq
  subst valuesRestore
  cases symbol <;>
    simp [TM2.step, program, restoreValuesCfg, pushRestoredValueCfg,
      emptyCfg, unaryCfg, cfg, tapes] <;>
    rfl

theorem step_restoreValues_nil (data : TapeData)
    (restoreEq : data.valuesRestore = []) :
    machine.step (restoreValuesCfg data) =
      some (scanRowsCfg { data with valuesRestore := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change valuesRestore = [] at restoreEq
  subst valuesRestore
  simp [TM2.step, program, restoreValuesCfg, scanRowsCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_pushRestoredValue (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushRestoredValueCfg symbol data) =
      some (restoreValuesCfg
        { data with values := symbol :: data.values }) := by
  cases symbol <;>
    simp [TM2.step, program, pushRestoredValueCfg, restoreValuesCfg,
      unaryCfg, emptyCfg, cfg, tapes] <;>
    rfl

theorem step_clearValues_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (valuesEq : data.values = symbol :: remaining) :
    machine.step (clearValuesCfg data) =
      some (clearValuesCfg { data with values := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change values = _ at valuesEq
  subst values
  cases symbol <;>
    simp [TM2.step, program, clearValuesCfg, emptyCfg, cfg, tapes] <;>
    rfl

theorem step_clearValues_nil (data : TapeData)
    (valuesEq : data.values = []) :
    machine.step (clearValuesCfg data) =
      some (reverseOutputCfg { data with values := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change values = [] at valuesEq
  subst values
  simp [TM2.step, program, clearValuesCfg, reverseOutputCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_reverseOutput_cons (data : TapeData) (symbol : UnarySymbol)
    (remaining : List UnarySymbol)
    (reverseEq : data.outputReverse = symbol :: remaining) :
    machine.step (reverseOutputCfg data) =
      some (pushOutputCfg symbol
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change outputReverse = _ at reverseEq
  subst outputReverse
  cases symbol <;>
    simp [TM2.step, program, reverseOutputCfg, pushOutputCfg,
      emptyCfg, unaryCfg, cfg, tapes] <;>
    rfl

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_pushOutput (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushOutputCfg symbol data) =
      some (reverseOutputCfg
        { data with output := symbol :: data.output }) := by
  cases symbol <;>
    simp [TM2.step, program, pushOutputCfg, reverseOutputCfg,
      unaryCfg, emptyCfg, cfg, tapes] <;>
    rfl

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
