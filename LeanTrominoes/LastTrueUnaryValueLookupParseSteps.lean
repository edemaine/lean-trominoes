/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTapes

/-! # Parsing steps of last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open Turing

attribute [local simp] initialState setInput setRow setUnary
  clearInput clearRow clearUnary inputIsNone inputIsLeft
  inputIsSeparator inputIsRight rowIsNone unaryIsNone inputState
  rowState unaryState

theorem step_scanLeft_left (data : TapeData) (symbol : RowSymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    machine.step (scanLeftCfg data) =
      some (pushRowReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, pushRowReverseCfg,
    emptyCfg, inputCfg, cfg, inputState, tapes,
    inputIsNone, inputIsLeft]
  rfl

theorem step_pushRowReverse (data : TapeData) (symbol : RowSymbol) :
    machine.step (pushRowReverseCfg symbol data) =
      some (scanLeftCfg
        { data with rowsReverse := symbol :: data.rowsReverse }) := by
  simp [TM2.step, program, pushRowReverseCfg, scanLeftCfg,
    inputCfg, inputState, emptyCfg, cfg, tapes, leftRow, clearInput]
  rfl

theorem step_scanLeft_separator (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg data) =
      some (scanRightCfg { data with input := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanLeftCfg, scanRightCfg, emptyCfg, cfg,
    tapes, inputIsNone, inputIsLeft, inputIsSeparator, clearInput]
  rfl

theorem step_scanRight_right (data : TapeData) (symbol : UnarySymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanRightCfg data) =
      some (pushValueReverseCfg symbol { data with input := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, pushValueReverseCfg,
    emptyCfg, inputCfg, cfg, inputState, tapes,
    inputIsNone, inputIsRight]
  rfl

theorem step_pushValueReverse (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushValueReverseCfg symbol data) =
      some (scanRightCfg
        { data with valuesReverse := symbol :: data.valuesReverse }) := by
  simp [TM2.step, program, pushValueReverseCfg, scanRightCfg,
    inputCfg, inputState, emptyCfg, cfg, tapes, rightUnary, clearInput]
  rfl

theorem step_scanRight_nil (data : TapeData)
    (inputEq : data.input = []) :
    machine.step (scanRightCfg data) =
      some (restoreRowsCfg { data with input := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanRightCfg, restoreRowsCfg,
    emptyCfg, cfg, tapes, inputIsNone, clearInput]
  rfl

theorem step_restoreRows_cons (data : TapeData) (symbol : RowSymbol)
    (remaining : List RowSymbol)
    (reverseEq : data.rowsReverse = symbol :: remaining) :
    machine.step (restoreRowsCfg data) =
      some (pushRowCfg symbol { data with rowsReverse := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rowsReverse = _ at reverseEq
  subst rowsReverse
  simp [TM2.step, program, restoreRowsCfg, pushRowCfg,
    emptyCfg, rowCfg, rowState, cfg, tapes, rowIsNone]
  rfl

theorem step_pushRow (data : TapeData) (symbol : RowSymbol) :
    machine.step (pushRowCfg symbol data) =
      some (restoreRowsCfg { data with rows := symbol :: data.rows }) := by
  simp [TM2.step, program, pushRowCfg, restoreRowsCfg,
    rowCfg, rowState, emptyCfg, cfg, tapes, storedRow, clearRow]
  rfl

theorem step_restoreRows_nil (data : TapeData)
    (reverseEq : data.rowsReverse = []) :
    machine.step (restoreRowsCfg data) =
      some (restoreInitialValuesCfg { data with rowsReverse := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rowsReverse = [] at reverseEq
  subst rowsReverse
  simp [TM2.step, program, restoreRowsCfg, restoreInitialValuesCfg,
    emptyCfg, cfg, tapes, rowIsNone, clearRow]
  rfl

theorem step_restoreInitialValues_cons (data : TapeData)
    (symbol : UnarySymbol) (remaining : List UnarySymbol)
    (reverseEq : data.valuesReverse = symbol :: remaining) :
    machine.step (restoreInitialValuesCfg data) =
      some (pushInitialValueCfg symbol
        { data with valuesReverse := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change valuesReverse = _ at reverseEq
  subst valuesReverse
  simp [TM2.step, program, restoreInitialValuesCfg, pushInitialValueCfg,
    emptyCfg, unaryCfg, unaryState, cfg, tapes, unaryIsNone]
  rfl

theorem step_pushInitialValue (data : TapeData) (symbol : UnarySymbol) :
    machine.step (pushInitialValueCfg symbol data) =
      some (restoreInitialValuesCfg
        { data with values := symbol :: data.values }) := by
  simp [TM2.step, program, pushInitialValueCfg,
    restoreInitialValuesCfg, unaryCfg, unaryState, emptyCfg, cfg, tapes,
    storedUnary, clearUnary]
  rfl

theorem step_restoreInitialValues_nil (data : TapeData)
    (reverseEq : data.valuesReverse = []) :
    machine.step (restoreInitialValuesCfg data) =
      some (scanRowsCfg { data with valuesReverse := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change valuesReverse = [] at reverseEq
  subst valuesReverse
  simp [TM2.step, program, restoreInitialValuesCfg, scanRowsCfg,
    emptyCfg, cfg, tapes, unaryIsNone, clearUnary]
  rfl

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
