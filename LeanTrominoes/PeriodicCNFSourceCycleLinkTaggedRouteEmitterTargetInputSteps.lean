/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates

/-! # Target-input parsing steps for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_scanTargetsInput_nil (tag : Tag) (data : TapeData)
    (inputEq : data.input = []) :
    machine.step (scanTargetsInputCfg tag data) =
      some (restoreTagsCfg tag { data with input := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanTargetsInputCfg,
    restoreTagsCfg, cursorCfg, cfg, program, TM2.stepAux,
    inputIsNone, cursorTag, clear, update_tapes_input]
  rfl

theorem step_scanTargetsInput_right (tag : Tag) (data : TapeData)
    (symbol : UnarySymbol) (remaining : List InputSymbol)
    (inputEq : data.input = .right symbol :: remaining) :
    machine.step (scanTargetsInputCfg tag data) =
      some (pushTargetReverseCfg tag (.right symbol)
        { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, scanTargetsInputCfg,
      pushTargetReverseCfg, cursorCfg, inputCfg, cfg, program, TM2.stepAux,
      inputIsNone, inputIsRight, cursorTag, update_tapes_input] <;>
    rfl

theorem step_scanTargetsInput_left (tag : Tag) (data : TapeData)
    (symbol : SourceCycleLinkTaggedRouteEmitter.HeaderSymbol)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left symbol :: remaining) :
    machine.step (scanTargetsInputCfg tag data) =
      some (scanTargetsInputCfg tag { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases symbol with
  | left symbol =>
    cases symbol <;>
      simp only [FinTM2.step, TM2.step, machine, scanTargetsInputCfg,
        cursorCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsRight,
        cursorTag, clear, update_tapes_input] <;>
      rfl
  | separator =>
      simp only [FinTM2.step, TM2.step, machine, scanTargetsInputCfg,
        cursorCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsRight,
        cursorTag, clear, update_tapes_input]
      rfl
  | right symbol =>
    cases symbol <;>
      simp only [FinTM2.step, TM2.step, machine, scanTargetsInputCfg,
        cursorCfg, cfg, program, TM2.stepAux, inputIsNone, inputIsRight,
        cursorTag, clear, update_tapes_input] <;>
      rfl

theorem step_pushTargetReverse (tag : Tag) (data : TapeData)
    (symbol : UnarySymbol) :
    machine.step (pushTargetReverseCfg tag (.right symbol) data) =
      some (scanTargetsInputCfg tag
        { data with targetReverse := symbol :: data.targetReverse }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  cases symbol <;>
    simp only [FinTM2.step, TM2.step, machine, pushTargetReverseCfg,
      inputCfg, scanTargetsInputCfg, cursorCfg, cfg, program, TM2.stepAux,
      unaryFromState, cursorTag, clear, update_tapes_targetReverse] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
