/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates

/-! # Right-input parsing steps for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_scanRight_nil (cursor : Cursor) (data : TapeData)
    (inputEq : data.input = []) :
    machine.step (scanRightCfg cursor data) =
      some (restoreOccurrencesCfg cursor { data with input := [] }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
    restoreOccurrencesCfg, cursorCfg, cfg, program, TM2.stepAux,
    inputIsNone, cursorFromState, clear, update_tapes_input]
  rfl

theorem step_scanRight_right (cursor : Cursor) (data : TapeData)
    (symbol : UnarySymbol) (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanRightCfg cursor data) =
      some (pushTargetReverseCfg cursor (.right symbol)
        { data with input := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, scanRightCfg,
      pushTargetReverseCfg, cursorCfg, inputCfg, cfg, program, TM2.stepAux,
      inputIsNone, inputIsRight, cursorFromState, update_tapes_input] <;>
    rfl

theorem step_pushTargetReverse (cursor : Cursor) (data : TapeData)
    (symbol : UnarySymbol) :
    machine.step (pushTargetReverseCfg cursor (.right symbol) data) =
      some (scanRightCfg cursor
        { data with targetReverse := symbol :: data.targetReverse }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, pushTargetReverseCfg,
      inputCfg, scanRightCfg, cursorCfg, cfg, program, TM2.stepAux,
      unaryFromState, cursorFromState, clear,
      update_tapes_targetReverse] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
