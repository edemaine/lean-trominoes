/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTapes

/-! # Row-control steps of last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open Turing

attribute [local simp] initialState setRow setUnary setCandidate clearRow
  clearUnary clearRowUnary clearCandidateState rowIsNone rowIsStart
  rowIsBit rowBitIsTrue candidateIsNone rowBitState rowState

theorem step_scanRows_nil (data : TapeData) (rowsEq : data.rows = []) :
    machine.step (scanRowsCfg data) =
      some (clearValuesCfg { data with rows := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rows = [] at rowsEq
  subst rows
  simp [TM2.step, program, scanRowsCfg, clearValuesCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_scanRows_start (data : TapeData)
    (remaining : List RowSymbol)
    (rowsEq : data.rows = .wordStart :: remaining) :
    machine.step (scanRowsCfg data) =
      some (nextBitCfg { data with rows := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rows = _ at rowsEq
  subst rows
  simp [TM2.step, program, scanRowsCfg, nextBitCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_nextBit_bit (data : TapeData) (selected : Bool)
    (remaining : List RowSymbol)
    (rowsEq : data.rows = .bit selected :: remaining) :
    machine.step (nextBitCfg data) =
      some (prepareValueCfg selected { data with rows := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rows = _ at rowsEq
  subst rows
  cases selected <;>
    simp [TM2.step, program, nextBitCfg, prepareValueCfg,
      emptyCfg, rowBitCfg, cfg, tapes, rowBitState] <;>
    rfl

theorem step_nextBit_end (data : TapeData)
    (remaining : List RowSymbol)
    (rowsEq : data.rows = .wordEnd :: remaining) :
    machine.step (nextBitCfg data) =
      some (drainCandidateCfg { data with rows := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change rows = _ at rowsEq
  subst rows
  simp [TM2.step, program, nextBitCfg, drainCandidateCfg,
    emptyCfg, cfg, tapes]
  rfl

theorem step_prepareValue_true (data : TapeData) :
    machine.step (prepareValueCfg true data) =
      some (clearCandidateCfg true data) := by
  simp [TM2.step, program, prepareValueCfg, clearCandidateCfg,
    rowBitCfg, rowBitState, cfg]
  rfl

theorem step_prepareValue_false (data : TapeData) :
    machine.step (prepareValueCfg false data) =
      some (readValueCfg false data) := by
  simp [TM2.step, program, prepareValueCfg, readValueCfg,
    rowBitCfg, rowBitState, cfg]
  rfl

theorem step_clearCandidate_cons (data : TapeData) (selected : Bool)
    (remaining : List Unit)
    (candidateEq : data.candidate = () :: remaining) :
    machine.step (clearCandidateCfg selected data) =
      some (clearCandidateCfg selected
        { data with candidate := remaining }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change candidate = _ at candidateEq
  subst candidate
  cases selected <;>
    simp [TM2.step, program, clearCandidateCfg, rowBitCfg,
      rowBitState, cfg, tapes] <;>
    rfl

theorem step_clearCandidate_nil (data : TapeData) (selected : Bool)
    (candidateEq : data.candidate = []) :
    machine.step (clearCandidateCfg selected data) =
      some (readValueCfg selected { data with candidate := [] }) := by
  rcases data with ⟨input, rowsReverse, rows, valuesReverse, values,
    valuesRestore, candidate, outputReverse, output⟩
  change candidate = [] at candidateEq
  subst candidate
  cases selected <;>
    simp [TM2.step, program, clearCandidateCfg, readValueCfg,
      rowBitCfg, rowBitState, cfg, tapes] <;>
    rfl

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
