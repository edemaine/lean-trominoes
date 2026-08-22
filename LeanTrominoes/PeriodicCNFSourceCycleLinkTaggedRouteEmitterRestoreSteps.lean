/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates

/-! # Stream-restoration steps for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_restoreTags_nil (tag : Tag) (data : TapeData)
    (reverseEq : data.tagReverse = []) :
    machine.step (restoreTagsCfg tag data) =
      some (restoreTargetsCfg tag { data with tagReverse := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change tagReverse = [] at reverseEq
  subst tagReverse
  simp only [FinTM2.step, TM2.step, machine, restoreTagsCfg,
    restoreTargetsCfg, cursorCfg, cfg, program, TM2.stepAux,
    tagIsNone, cursorTag, clear, update_tapes_tagReverse]
  rfl

theorem step_restoreTags_cons (cursor current : Tag) (data : TapeData)
    (remaining : List Tag)
    (reverseEq : data.tagReverse = current :: remaining) :
    machine.step (restoreTagsCfg cursor data) =
      some (pushTagForwardCfg cursor current
        { data with tagReverse := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change tagReverse = _ at reverseEq
  subst tagReverse
  cases current <;>
    simp only [FinTM2.step, TM2.step, machine, restoreTagsCfg,
      pushTagForwardCfg, cursorCfg, tagCfg, cfg, program, TM2.stepAux,
      tagIsNone, cursorTag, update_tapes_tagReverse] <;>
    rfl

theorem step_pushTagForward (cursor current : Tag) (data : TapeData) :
    machine.step (pushTagForwardCfg cursor current data) =
      some (restoreTagsCfg cursor
        { data with tags := current :: data.tags }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  cases current <;>
    simp only [FinTM2.step, TM2.step, machine, pushTagForwardCfg,
      tagCfg, restoreTagsCfg, cursorCfg, cfg, program, TM2.stepAux,
      tagFromState, cursorTag, clear, update_tapes_tags] <;>
    rfl

theorem step_restoreTargets_nil (tag : Tag) (data : TapeData)
    (reverseEq : data.targetReverse = []) :
    machine.step (restoreTargetsCfg tag data) =
      some (scanLinksCfg tag { data with targetReverse := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change targetReverse = [] at reverseEq
  subst targetReverse
  simp only [FinTM2.step, TM2.step, machine, restoreTargetsCfg,
    scanLinksCfg, cursorCfg, cfg, program, TM2.stepAux,
    unaryIsNone, cursorTag, clear, update_tapes_targetReverse]
  rfl

theorem step_restoreTargets_cons (tag : Tag) (data : TapeData)
    (symbol : UnarySymbol) (remaining : List UnarySymbol)
    (reverseEq : data.targetReverse = symbol :: remaining) :
    machine.step (restoreTargetsCfg tag data) =
      some (pushTargetForwardCfg tag symbol
        { data with targetReverse := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change targetReverse = _ at reverseEq
  subst targetReverse
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, restoreTargetsCfg,
      pushTargetForwardCfg, cursorCfg, unaryCfg, cfg, program, TM2.stepAux,
      unaryIsNone, cursorTag, update_tapes_targetReverse] <;>
    rfl

theorem step_pushTargetForward (tag : Tag) (data : TapeData)
    (symbol : UnarySymbol) :
    machine.step (pushTargetForwardCfg tag symbol data) =
      some (restoreTargetsCfg tag
        { data with targets := symbol :: data.targets }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, pushTargetForwardCfg,
      unaryCfg, restoreTargetsCfg, cursorCfg, cfg, program, TM2.stepAux,
      unaryFromState, cursorTag, clear, update_tapes_targets] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
