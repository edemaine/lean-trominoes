/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCleanupData
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterOutputTapeUpdates

/-! # One-step transitions for final route-emitter cleanup -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open Turing

theorem step_cleanup_nil (stage : CleanupStage) (cursor : Cursor)
    (data : TapeData) (symbolsEq : stage.symbols data = []) :
    machine.step (cleanupCfg stage cursor data) =
      some (stage.afterCfg cursor data) := by
  cases stage <;>
    rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
      targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
      outputReverse, output⟩ <;>
    simp only [CleanupStage.symbols] at symbolsEq <;>
    subst_vars <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupCfg, cursorCfg, cfg,
      program, TM2.stepAux, CleanupStage.stack, CleanupStage.read,
      cleanupIsNone, afterCleanup, CleanupStage.afterCfg,
      CleanupStage.cleared, CleanupStage.set, haltDataCfg,
      tapes, List.head?_nil, List.tail_nil, cursorFromState, clear,
      update_tapes_input, update_tapes_occurrenceReverse,
      update_tapes_occurrences, update_tapes_targetReverse,
      update_tapes_targets, update_tapes_clauseCount,
      update_tapes_literalCount, update_tapes_clauseIndex,
      update_tapes_edgeIndex, update_tapes_scratch,
      update_tapes_outputReverse] <;>
    simp <;> rfl

theorem step_cleanup_cons (stage : CleanupStage) (cursor : Cursor)
    (data : TapeData) (token : Alphabet stage.stack)
    (remaining : List (Alphabet stage.stack))
    (symbolsEq : stage.symbols data = token :: remaining) :
    machine.step (cleanupCfg stage cursor data) =
      some (cleanupCfg stage cursor (stage.set data remaining)) := by
  cases stage <;>
    rcases data with ⟨input, occurrenceReverse, occurrences, targetReverse,
      targets, clauseCount, literalCount, clauseIndex, edgeIndex, scratch,
      outputReverse, output⟩ <;>
    simp only [CleanupStage.symbols] at symbolsEq <;>
    subst_vars <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupCfg, cursorCfg, cfg,
      program, TM2.stepAux, CleanupStage.stack, CleanupStage.read,
      cleanupIsNone, CleanupStage.set, tapes,
      List.head?_cons, List.tail_cons, cursorFromState, clear,
      update_tapes_input, update_tapes_occurrenceReverse,
      update_tapes_occurrences, update_tapes_targetReverse,
      update_tapes_targets, update_tapes_clauseCount,
      update_tapes_literalCount, update_tapes_clauseIndex,
      update_tapes_edgeIndex, update_tapes_scratch,
      update_tapes_outputReverse] <;>
    simp <;> rfl

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
