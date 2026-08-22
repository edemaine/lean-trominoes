/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCleanupData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # One-step transitions for final tagged cycle-link cleanup -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_cleanup_nil (stage : CleanupStage) (tag : Tag)
    (data : TapeData) (symbolsEq : stage.symbols data = []) :
    machine.step (cleanupCfg stage tag data) =
      some (stage.afterCfg tag data) := by
  cases stage <;>
    rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
      clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩ <;>
    simp only [CleanupStage.symbols] at symbolsEq <;>
    subst_vars <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupCfg, cursorCfg, cfg,
      program, TM2.stepAux, CleanupStage.stack, CleanupStage.read,
      cleanupIsNone, afterCleanup, CleanupStage.afterCfg,
      CleanupStage.cleared, CleanupStage.set, haltDataCfg,
      tapes, List.head?_nil, List.tail_nil, cursorTag, clear,
      update_tapes_input, update_tapes_tagReverse, update_tapes_tags,
      update_tapes_targetReverse, update_tapes_targets,
      update_tapes_clauseCount, update_tapes_literalCount,
      update_tapes_linkIndex, update_tapes_scratch,
      update_tapes_outputReverse] <;>
    simp <;> rfl

theorem step_cleanup_cons (stage : CleanupStage) (tag : Tag)
    (data : TapeData) (token : Alphabet stage.stack)
    (remaining : List (Alphabet stage.stack))
    (symbolsEq : stage.symbols data = token :: remaining) :
    machine.step (cleanupCfg stage tag data) =
      some (cleanupCfg stage tag (stage.set data remaining)) := by
  cases stage <;>
    rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
      clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩ <;>
    simp only [CleanupStage.symbols] at symbolsEq <;>
    subst_vars <;>
    simp only [FinTM2.step, TM2.step, machine, cleanupCfg, cursorCfg, cfg,
      program, TM2.stepAux, CleanupStage.stack, CleanupStage.read,
      cleanupIsNone, CleanupStage.set, tapes,
      List.head?_cons, List.tail_cons, cursorTag, clear,
      update_tapes_input, update_tapes_tagReverse, update_tapes_tags,
      update_tapes_targetReverse, update_tapes_targets,
      update_tapes_clauseCount, update_tapes_literalCount,
      update_tapes_linkIndex, update_tapes_scratch,
      update_tapes_outputReverse] <;>
    simp <;> rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
