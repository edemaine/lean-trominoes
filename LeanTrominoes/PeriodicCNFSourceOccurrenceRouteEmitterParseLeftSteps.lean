/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates

/-! # Left-input parsing steps for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_scanLeft_left (cursor : Cursor) (data : TapeData)
    (token : OccurrenceToken) (remaining : List InputSymbol)
    (inputEq : data.input = .left token :: remaining) :
    machine.step (scanLeftCfg cursor data) =
      some (pushOccurrenceCfg cursor (.left token)
        { data with input := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, cursorCfg, cfg,
    program, TM2.stepAux, inputIsNone, inputIsLeft, cursorFromState,
    update_tapes_input]
  rfl

theorem step_scanLeft_separator (cursor : Cursor) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanLeftCfg cursor data) =
      some (scanRightCfg cursor { data with input := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanLeftCfg, scanRightCfg,
    cursorCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsLeft,
    inputIsSeparator, cursorFromState, clear, update_tapes_input]
  rfl

theorem step_pushOccurrence_clause (cursor : Cursor) (data : TapeData)
    (arity : Fin 4) :
    machine.step
        (pushOccurrenceCfg cursor (.left (.clause arity)) data) =
      some (scanLeftCfg cursor
        { data with
          occurrenceReverse := .clause arity :: data.occurrenceReverse
          clauseCount := () :: data.clauseCount }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushOccurrenceCfg, inputCfg,
    scanLeftCfg, cursorCfg, cfg, program, TM2.stepAux,
    occurrenceFromState, inputLeftIsClause, cursorFromState, clear,
    update_tapes_occurrenceReverse, update_tapes_clauseCount]
  rfl

theorem step_pushOccurrence_literal (cursor : Cursor) (data : TapeData)
    (index : Fin 3) :
    machine.step
        (pushOccurrenceCfg cursor (.left (.literal index)) data) =
      some (scanLeftCfg cursor
        { data with
          occurrenceReverse := .literal index :: data.occurrenceReverse
          literalCount := () :: data.literalCount }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushOccurrenceCfg, inputCfg,
    scanLeftCfg, cursorCfg, cfg, program, TM2.stepAux,
    occurrenceFromState, inputLeftIsClause, inputLeftIsLiteral,
    cursorFromState, clear, update_tapes_occurrenceReverse,
    update_tapes_literalCount]
  rfl

theorem step_pushOccurrence_offset (cursor : Cursor) (data : TapeData)
    (value : Bool) :
    machine.step
        (pushOccurrenceCfg cursor (.left (.offsetNext value)) data) =
      some (scanLeftCfg cursor
        { data with
          occurrenceReverse :=
            .offsetNext value :: data.occurrenceReverse }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  cases value <;>
    simp only [FinTM2.step, TM2.step, machine, pushOccurrenceCfg, inputCfg,
      scanLeftCfg, cursorCfg, cfg, program, TM2.stepAux,
      occurrenceFromState, inputLeftIsClause, inputLeftIsLiteral,
      cursorFromState, clear, update_tapes_occurrenceReverse] <;>
    rfl

theorem step_pushOccurrence_literalEnd (cursor : Cursor) (data : TapeData) :
    machine.step
        (pushOccurrenceCfg cursor (.left .literalEnd) data) =
      some (scanLeftCfg cursor
        { data with
          occurrenceReverse := .literalEnd :: data.occurrenceReverse }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushOccurrenceCfg, inputCfg,
    scanLeftCfg, cursorCfg, cfg, program, TM2.stepAux,
    occurrenceFromState, inputLeftIsClause, inputLeftIsLiteral,
    cursorFromState, clear, update_tapes_occurrenceReverse]
  rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
