/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates

/-! # Header-parsing steps for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_scanHeader_nil (tag : Tag) (data : TapeData)
    (inputEq : data.input = []) :
    machine.step (scanHeaderCfg tag data) =
      some (restoreTagsCfg tag { data with input := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg,
    restoreTagsCfg, cursorCfg, cfg, program, TM2.stepAux,
    inputIsNone, cursorTag, clear, update_tapes_input]
  rfl

theorem step_scanHeader_outerSeparator (tag : Tag) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .separator :: remaining) :
    machine.step (scanHeaderCfg tag data) =
      some (scanTargetsInputCfg tag { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg,
    scanTargetsInputCfg, cursorCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputIsOuterSeparator, cursorTag, clear,
    update_tapes_input]
  rfl

theorem step_scanHeader_clauseUnit (tag : Tag) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left (.left .unit) :: remaining) :
    machine.step (scanHeaderCfg tag data) =
      some (pushClauseUnitCfg tag (.left (.left .unit))
        { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg,
    pushClauseUnitCfg, cursorCfg, inputCfg, cfg, program, TM2.stepAux,
    inputIsNone, inputIsOuterSeparator, inputIsClauseUnit, cursorTag,
    update_tapes_input]
  rfl

theorem step_pushClauseUnit (tag : Tag) (data : TapeData) :
    machine.step
        (pushClauseUnitCfg tag (.left (.left .unit)) data) =
      some (scanHeaderCfg tag
        { data with clauseCount := () :: data.clauseCount }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushClauseUnitCfg,
    inputCfg, scanHeaderCfg, cursorCfg, cfg, program, TM2.stepAux,
    cursorTag, clear, update_tapes_clauseCount]
  rfl

theorem step_scanHeader_clauseDelimiter (tag : Tag) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left (.left .delimiter) :: remaining) :
    machine.step (scanHeaderCfg tag data) =
      some (scanHeaderCfg tag { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg, cursorCfg,
    cfg, program, TM2.stepAux, inputIsNone, inputIsOuterSeparator,
    inputIsClauseUnit, inputIsTag, cursorTag, clear, update_tapes_input]
  rfl

theorem step_scanHeader_innerSeparator (tag : Tag) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left .separator :: remaining) :
    machine.step (scanHeaderCfg tag data) =
      some (scanHeaderCfg tag { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg, cursorCfg,
    cfg, program, TM2.stepAux, inputIsNone, inputIsOuterSeparator,
    inputIsClauseUnit, inputIsTag, cursorTag, clear, update_tapes_input]
  rfl

theorem step_scanHeader_tag (cursor current : Tag) (data : TapeData)
    (remaining : List InputSymbol)
    (inputEq : data.input = .left (.right current) :: remaining) :
    machine.step (scanHeaderCfg cursor data) =
      some (pushTagReverseCfg cursor (.left (.right current))
        { data with input := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change input = _ at inputEq
  subst input
  cases current <;>
    simp only [FinTM2.step, TM2.step, machine, scanHeaderCfg,
      pushTagReverseCfg, cursorCfg, inputCfg, cfg, program, TM2.stepAux,
      inputIsNone, inputIsOuterSeparator, inputIsClauseUnit, inputIsTag,
      cursorTag, update_tapes_input] <;>
    rfl

theorem step_pushTagReverse (cursor current : Tag) (data : TapeData) :
    machine.step
        (pushTagReverseCfg cursor (.left (.right current)) data) =
      some (scanHeaderCfg cursor
        { data with
          tagReverse := current :: data.tagReverse
          literalCount := () :: data.literalCount }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  cases current <;>
    simp only [FinTM2.step, TM2.step, machine, pushTagReverseCfg,
      inputCfg, scanHeaderCfg, cursorCfg, cfg, program, TM2.stepAux,
      tagFromState, cursorTag, clear, update_tapes_tagReverse,
      update_tapes_literalCount] <;>
    rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
