/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupRowSteps

/-! # Unary-value transfer steps of last-true lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open Turing

attribute [local simp] initialState setUnary clearUnary clearRowUnary
  unaryIsNone unaryIsUnit rowBitIsTrue rowBitState rowUnaryState
  unaryState storedUnary

theorem step_readValue_cons (data : TapeData) (selected : Bool)
    (symbol : UnarySymbol) (remaining : List UnarySymbol)
    (valuesEq : data.values = symbol :: remaining) :
    machine.step (readValueCfg selected data) =
      some (pushValueRestoreCfg selected symbol
        { data with values := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change values = _ at valuesEq
  subst values
  cases selected <;> cases symbol <;>
    simp [TM2.step, program, readValueCfg, pushValueRestoreCfg,
      rowBitCfg, rowUnaryCfg, cfg, tapes] <;>
    rfl

theorem step_readValue_nil (data : TapeData) (selected : Bool)
    (valuesEq : data.values = []) :
    machine.step (readValueCfg selected data) =
      some (nextBitCfg { data with values := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change values = [] at valuesEq
  subst values
  cases selected <;>
    simp [TM2.step, program, readValueCfg, nextBitCfg,
      rowBitCfg, emptyCfg, cfg, tapes] <;>
    rfl

theorem step_pushValueRestore_unit_true (data : TapeData) :
    machine.step (pushValueRestoreCfg true .unit data) =
      some (pushCandidateUnitCfg
        { data with valuesRestore := .unit :: data.valuesRestore }) := by
  simp [TM2.step, program, pushValueRestoreCfg, pushCandidateUnitCfg,
    rowUnaryCfg, cfg, tapes]
  rfl

theorem step_pushValueRestore_unit_false (data : TapeData) :
    machine.step (pushValueRestoreCfg false .unit data) =
      some (readValueCfg false
        { data with valuesRestore := .unit :: data.valuesRestore }) := by
  simp [TM2.step, program, pushValueRestoreCfg, readValueCfg,
    rowUnaryCfg, rowBitCfg, cfg, tapes]
  rfl

theorem step_pushValueRestore_delimiter (data : TapeData)
    (selected : Bool) :
    machine.step (pushValueRestoreCfg selected .delimiter data) =
      some (nextBitCfg
        { data with valuesRestore := .delimiter :: data.valuesRestore }) := by
  cases selected <;>
    simp [TM2.step, program, pushValueRestoreCfg, nextBitCfg,
      rowUnaryCfg, emptyCfg, cfg, tapes] <;>
    rfl

theorem step_pushCandidateUnit (data : TapeData) :
    machine.step (pushCandidateUnitCfg data) =
      some (readValueCfg true
        { data with candidate := () :: data.candidate }) := by
  simp [TM2.step, program, pushCandidateUnitCfg, readValueCfg,
    rowUnaryCfg, rowBitCfg, cfg, tapes, clearUnary]
  rfl

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
