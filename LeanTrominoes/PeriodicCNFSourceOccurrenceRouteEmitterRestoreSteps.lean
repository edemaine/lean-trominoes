/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates

/-! # Stream-restoration steps for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_restoreOccurrences_nil (cursor : Cursor) (data : TapeData)
    (reverseEq : data.occurrenceReverse = []) :
    machine.step (restoreOccurrencesCfg cursor data) =
      some (restoreTargetsCfg cursor
        { data with occurrenceReverse := [] }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrenceReverse = [] at reverseEq
  subst occurrenceReverse
  simp only [FinTM2.step, TM2.step, machine, restoreOccurrencesCfg,
    restoreTargetsCfg, cursorCfg, cfg, program, TM2.stepAux,
    occurrenceIsNone, cursorFromState, clear,
    update_tapes_occurrenceReverse]
  rfl

theorem step_restoreOccurrences_cons (cursor : Cursor) (data : TapeData)
    (token : OccurrenceToken) (remaining : List OccurrenceToken)
    (reverseEq : data.occurrenceReverse = token :: remaining) :
    machine.step (restoreOccurrencesCfg cursor data) =
      some (pushOccurrenceForwardCfg cursor token
        { data with occurrenceReverse := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change occurrenceReverse = _ at reverseEq
  subst occurrenceReverse
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, restoreOccurrencesCfg,
      pushOccurrenceForwardCfg, cursorCfg, occurrenceCfg, cfg, program,
      TM2.stepAux, occurrenceIsNone, cursorFromState,
      update_tapes_occurrenceReverse] <;>
    rfl

theorem step_pushOccurrenceForward (cursor : Cursor) (data : TapeData)
    (token : OccurrenceToken) :
    machine.step (pushOccurrenceForwardCfg cursor token data) =
      some (restoreOccurrencesCfg cursor
        { data with occurrences := token :: data.occurrences }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  cases token <;>
    simp only [FinTM2.step, TM2.step, machine, pushOccurrenceForwardCfg,
      occurrenceCfg, restoreOccurrencesCfg, cursorCfg, cfg, program,
      TM2.stepAux, occurrenceFromState, cursorFromState, clear,
      update_tapes_occurrences] <;>
    rfl

theorem step_restoreTargets_nil (cursor : Cursor) (data : TapeData)
    (reverseEq : data.targetReverse = []) :
    machine.step (restoreTargetsCfg cursor data) =
      some (scanOccurrencesCfg cursor
        { data with targetReverse := [] }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change targetReverse = [] at reverseEq
  subst targetReverse
  simp only [FinTM2.step, TM2.step, machine, restoreTargetsCfg,
    scanOccurrencesCfg, cursorCfg, cfg, program, TM2.stepAux,
    unaryIsNone, cursorFromState, clear, update_tapes_targetReverse]
  rfl

theorem step_restoreTargets_cons (cursor : Cursor) (data : TapeData)
    (symbol : UnarySymbol) (remaining : List UnarySymbol)
    (reverseEq : data.targetReverse = symbol :: remaining) :
    machine.step (restoreTargetsCfg cursor data) =
      some (pushTargetForwardCfg cursor symbol
        { data with targetReverse := remaining }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  change targetReverse = _ at reverseEq
  subst targetReverse
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, restoreTargetsCfg,
      pushTargetForwardCfg, cursorCfg, unaryCfg, cfg, program, TM2.stepAux,
      unaryIsNone, cursorFromState, update_tapes_targetReverse] <;>
    rfl

theorem step_pushTargetForward (cursor : Cursor) (data : TapeData)
    (symbol : UnarySymbol) :
    machine.step (pushTargetForwardCfg cursor symbol data) =
      some (restoreTargetsCfg cursor
        { data with targets := symbol :: data.targets }) := by
  rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
    targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
    outputReverse, output⟩
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, pushTargetForwardCfg,
      unaryCfg, restoreTargetsCfg, cursorCfg, cfg, program, TM2.stepAux,
      unaryFromState, cursorFromState, clear, update_tapes_targets] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
